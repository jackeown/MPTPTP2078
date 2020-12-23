%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sSgcSPrRNJ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:58 EST 2020

% Result     : Theorem 5.52s
% Output     : Refutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 206 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :   28
%              Number of atoms          :  622 (1644 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X21 ) )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X14 )
      | ( r1_ordinal1 @ X13 @ X14 )
      | ( r1_ordinal1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ~ ( v3_ordinal1 @ X17 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_ordinal1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('9',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('16',plain,(
    ! [X21: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X21 ) )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('17',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ~ ( v3_ordinal1 @ X17 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_ordinal1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('19',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('31',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['14','29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','31'])).

thf('33',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ~ ( v3_ordinal1 @ X17 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_ordinal1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('38',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('46',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('47',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['14','29','30'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) ) @ sk_B )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('53',plain,(
    ! [X15: $i] :
      ( ( k1_ordinal1 @ X15 )
      = ( k2_xboole_0 @ X15 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('54',plain,(
    ! [X15: $i] :
      ( ( k1_ordinal1 @ X15 )
      = ( k2_xboole_0 @ X15 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('55',plain,(
    ! [X15: $i] :
      ( ( k1_ordinal1 @ X15 )
      = ( k2_xboole_0 @ X15 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('62',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('66',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['14','29'])).

thf('67',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['64','67'])).

thf('69',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','68'])).

thf('70',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sSgcSPrRNJ
% 0.14/0.36  % Computer   : n017.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:53:47 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 5.52/5.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.52/5.73  % Solved by: fo/fo7.sh
% 5.52/5.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.52/5.73  % done 5530 iterations in 5.270s
% 5.52/5.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.52/5.73  % SZS output start Refutation
% 5.52/5.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.52/5.73  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 5.52/5.73  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 5.52/5.73  thf(sk_A_type, type, sk_A: $i).
% 5.52/5.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.52/5.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.52/5.73  thf(sk_B_type, type, sk_B: $i).
% 5.52/5.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.52/5.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.52/5.73  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 5.52/5.73  thf(t29_ordinal1, axiom,
% 5.52/5.73    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 5.52/5.73  thf('0', plain,
% 5.52/5.73      (![X21 : $i]:
% 5.52/5.73         ((v3_ordinal1 @ (k1_ordinal1 @ X21)) | ~ (v3_ordinal1 @ X21))),
% 5.52/5.73      inference('cnf', [status(esa)], [t29_ordinal1])).
% 5.52/5.73  thf(d3_tarski, axiom,
% 5.52/5.73    (![A:$i,B:$i]:
% 5.52/5.73     ( ( r1_tarski @ A @ B ) <=>
% 5.52/5.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.52/5.73  thf('1', plain,
% 5.52/5.73      (![X1 : $i, X3 : $i]:
% 5.52/5.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.52/5.73      inference('cnf', [status(esa)], [d3_tarski])).
% 5.52/5.73  thf(d3_xboole_0, axiom,
% 5.52/5.73    (![A:$i,B:$i,C:$i]:
% 5.52/5.73     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 5.52/5.73       ( ![D:$i]:
% 5.52/5.73         ( ( r2_hidden @ D @ C ) <=>
% 5.52/5.73           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.52/5.73  thf('2', plain,
% 5.52/5.73      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.52/5.73         (~ (r2_hidden @ X8 @ X6)
% 5.52/5.73          | (r2_hidden @ X8 @ X7)
% 5.52/5.73          | (r2_hidden @ X8 @ X5)
% 5.52/5.73          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 5.52/5.73      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.52/5.73  thf('3', plain,
% 5.52/5.73      (![X5 : $i, X7 : $i, X8 : $i]:
% 5.52/5.73         ((r2_hidden @ X8 @ X5)
% 5.52/5.73          | (r2_hidden @ X8 @ X7)
% 5.52/5.73          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 5.52/5.73      inference('simplify', [status(thm)], ['2'])).
% 5.52/5.73  thf('4', plain,
% 5.52/5.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.52/5.73         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 5.52/5.73          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 5.52/5.73          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 5.52/5.73      inference('sup-', [status(thm)], ['1', '3'])).
% 5.52/5.73  thf(connectedness_r1_ordinal1, axiom,
% 5.52/5.73    (![A:$i,B:$i]:
% 5.52/5.73     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 5.52/5.73       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 5.52/5.73  thf('5', plain,
% 5.52/5.73      (![X13 : $i, X14 : $i]:
% 5.52/5.73         (~ (v3_ordinal1 @ X13)
% 5.52/5.73          | ~ (v3_ordinal1 @ X14)
% 5.52/5.73          | (r1_ordinal1 @ X13 @ X14)
% 5.52/5.73          | (r1_ordinal1 @ X14 @ X13))),
% 5.52/5.73      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 5.52/5.73  thf(redefinition_r1_ordinal1, axiom,
% 5.52/5.73    (![A:$i,B:$i]:
% 5.52/5.73     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 5.52/5.73       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 5.52/5.73  thf('6', plain,
% 5.52/5.73      (![X16 : $i, X17 : $i]:
% 5.52/5.73         (~ (v3_ordinal1 @ X16)
% 5.52/5.73          | ~ (v3_ordinal1 @ X17)
% 5.52/5.73          | (r1_tarski @ X16 @ X17)
% 5.52/5.73          | ~ (r1_ordinal1 @ X16 @ X17))),
% 5.52/5.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.52/5.73  thf('7', plain,
% 5.52/5.73      (![X0 : $i, X1 : $i]:
% 5.52/5.73         ((r1_ordinal1 @ X0 @ X1)
% 5.52/5.73          | ~ (v3_ordinal1 @ X0)
% 5.52/5.73          | ~ (v3_ordinal1 @ X1)
% 5.52/5.73          | (r1_tarski @ X1 @ X0)
% 5.52/5.73          | ~ (v3_ordinal1 @ X0)
% 5.52/5.73          | ~ (v3_ordinal1 @ X1))),
% 5.52/5.73      inference('sup-', [status(thm)], ['5', '6'])).
% 5.52/5.73  thf('8', plain,
% 5.52/5.73      (![X0 : $i, X1 : $i]:
% 5.52/5.73         ((r1_tarski @ X1 @ X0)
% 5.52/5.73          | ~ (v3_ordinal1 @ X1)
% 5.52/5.73          | ~ (v3_ordinal1 @ X0)
% 5.52/5.73          | (r1_ordinal1 @ X0 @ X1))),
% 5.52/5.73      inference('simplify', [status(thm)], ['7'])).
% 5.52/5.73  thf(t33_ordinal1, conjecture,
% 5.52/5.73    (![A:$i]:
% 5.52/5.73     ( ( v3_ordinal1 @ A ) =>
% 5.52/5.73       ( ![B:$i]:
% 5.52/5.73         ( ( v3_ordinal1 @ B ) =>
% 5.52/5.73           ( ( r2_hidden @ A @ B ) <=>
% 5.52/5.73             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 5.52/5.73  thf(zf_stmt_0, negated_conjecture,
% 5.52/5.73    (~( ![A:$i]:
% 5.52/5.73        ( ( v3_ordinal1 @ A ) =>
% 5.52/5.73          ( ![B:$i]:
% 5.52/5.73            ( ( v3_ordinal1 @ B ) =>
% 5.52/5.73              ( ( r2_hidden @ A @ B ) <=>
% 5.52/5.73                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 5.52/5.73    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 5.52/5.73  thf('9', plain,
% 5.52/5.73      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('10', plain,
% 5.52/5.73      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.52/5.73      inference('split', [status(esa)], ['9'])).
% 5.52/5.73  thf(t7_ordinal1, axiom,
% 5.52/5.73    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.52/5.73  thf('11', plain,
% 5.52/5.73      (![X22 : $i, X23 : $i]:
% 5.52/5.73         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 5.52/5.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.52/5.73  thf('12', plain,
% 5.52/5.73      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.52/5.73      inference('sup-', [status(thm)], ['10', '11'])).
% 5.52/5.73  thf('13', plain,
% 5.52/5.73      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.52/5.73        | ~ (r2_hidden @ sk_A @ sk_B))),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('14', plain,
% 5.52/5.73      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 5.52/5.73       ~ ((r2_hidden @ sk_A @ sk_B))),
% 5.52/5.73      inference('split', [status(esa)], ['13'])).
% 5.52/5.73  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 5.52/5.73  thf('15', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_ordinal1 @ X18))),
% 5.52/5.73      inference('cnf', [status(esa)], [t10_ordinal1])).
% 5.52/5.73  thf('16', plain,
% 5.52/5.73      (![X21 : $i]:
% 5.52/5.73         ((v3_ordinal1 @ (k1_ordinal1 @ X21)) | ~ (v3_ordinal1 @ X21))),
% 5.52/5.73      inference('cnf', [status(esa)], [t29_ordinal1])).
% 5.52/5.73  thf('17', plain,
% 5.52/5.73      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.52/5.73         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.52/5.73      inference('split', [status(esa)], ['9'])).
% 5.52/5.73  thf('18', plain,
% 5.52/5.73      (![X16 : $i, X17 : $i]:
% 5.52/5.73         (~ (v3_ordinal1 @ X16)
% 5.52/5.73          | ~ (v3_ordinal1 @ X17)
% 5.52/5.73          | (r1_tarski @ X16 @ X17)
% 5.52/5.73          | ~ (r1_ordinal1 @ X16 @ X17))),
% 5.52/5.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.52/5.73  thf('19', plain,
% 5.52/5.73      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.52/5.73         | ~ (v3_ordinal1 @ sk_B)
% 5.52/5.73         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 5.52/5.73         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.52/5.73      inference('sup-', [status(thm)], ['17', '18'])).
% 5.52/5.73  thf('20', plain, ((v3_ordinal1 @ sk_B)),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('21', plain,
% 5.52/5.73      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.52/5.73         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 5.52/5.73         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.52/5.73      inference('demod', [status(thm)], ['19', '20'])).
% 5.52/5.73  thf('22', plain,
% 5.52/5.73      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 5.52/5.73         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.52/5.73      inference('sup-', [status(thm)], ['16', '21'])).
% 5.52/5.73  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('24', plain,
% 5.52/5.73      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.52/5.73         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.52/5.73      inference('demod', [status(thm)], ['22', '23'])).
% 5.52/5.73  thf('25', plain,
% 5.52/5.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.52/5.73         (~ (r2_hidden @ X0 @ X1)
% 5.52/5.73          | (r2_hidden @ X0 @ X2)
% 5.52/5.73          | ~ (r1_tarski @ X1 @ X2))),
% 5.52/5.73      inference('cnf', [status(esa)], [d3_tarski])).
% 5.52/5.73  thf('26', plain,
% 5.52/5.73      ((![X0 : $i]:
% 5.52/5.73          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 5.52/5.73         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.52/5.73      inference('sup-', [status(thm)], ['24', '25'])).
% 5.52/5.73  thf('27', plain,
% 5.52/5.73      (((r2_hidden @ sk_A @ sk_B))
% 5.52/5.73         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.52/5.73      inference('sup-', [status(thm)], ['15', '26'])).
% 5.52/5.73  thf('28', plain,
% 5.52/5.73      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 5.52/5.73      inference('split', [status(esa)], ['13'])).
% 5.52/5.73  thf('29', plain,
% 5.52/5.73      (((r2_hidden @ sk_A @ sk_B)) | 
% 5.52/5.73       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 5.52/5.73      inference('sup-', [status(thm)], ['27', '28'])).
% 5.52/5.73  thf('30', plain,
% 5.52/5.73      (((r2_hidden @ sk_A @ sk_B)) | 
% 5.52/5.73       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 5.52/5.73      inference('split', [status(esa)], ['9'])).
% 5.52/5.73  thf('31', plain, (((r2_hidden @ sk_A @ sk_B))),
% 5.52/5.73      inference('sat_resolution*', [status(thm)], ['14', '29', '30'])).
% 5.52/5.73  thf('32', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 5.52/5.73      inference('simpl_trail', [status(thm)], ['12', '31'])).
% 5.52/5.73  thf('33', plain,
% 5.52/5.73      (((r1_ordinal1 @ sk_A @ sk_B)
% 5.52/5.73        | ~ (v3_ordinal1 @ sk_A)
% 5.52/5.73        | ~ (v3_ordinal1 @ sk_B))),
% 5.52/5.73      inference('sup-', [status(thm)], ['8', '32'])).
% 5.52/5.73  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('35', plain, ((v3_ordinal1 @ sk_B)),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('36', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 5.52/5.73      inference('demod', [status(thm)], ['33', '34', '35'])).
% 5.52/5.73  thf('37', plain,
% 5.52/5.73      (![X16 : $i, X17 : $i]:
% 5.52/5.73         (~ (v3_ordinal1 @ X16)
% 5.52/5.73          | ~ (v3_ordinal1 @ X17)
% 5.52/5.73          | (r1_tarski @ X16 @ X17)
% 5.52/5.73          | ~ (r1_ordinal1 @ X16 @ X17))),
% 5.52/5.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.52/5.73  thf('38', plain,
% 5.52/5.73      (((r1_tarski @ sk_A @ sk_B)
% 5.52/5.73        | ~ (v3_ordinal1 @ sk_B)
% 5.52/5.73        | ~ (v3_ordinal1 @ sk_A))),
% 5.52/5.73      inference('sup-', [status(thm)], ['36', '37'])).
% 5.52/5.73  thf('39', plain, ((v3_ordinal1 @ sk_B)),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('40', plain, ((v3_ordinal1 @ sk_A)),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('41', plain, ((r1_tarski @ sk_A @ sk_B)),
% 5.52/5.73      inference('demod', [status(thm)], ['38', '39', '40'])).
% 5.52/5.73  thf('42', plain,
% 5.52/5.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.52/5.73         (~ (r2_hidden @ X0 @ X1)
% 5.52/5.73          | (r2_hidden @ X0 @ X2)
% 5.52/5.73          | ~ (r1_tarski @ X1 @ X2))),
% 5.52/5.73      inference('cnf', [status(esa)], [d3_tarski])).
% 5.52/5.73  thf('43', plain,
% 5.52/5.73      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 5.52/5.73      inference('sup-', [status(thm)], ['41', '42'])).
% 5.52/5.73  thf('44', plain,
% 5.52/5.73      (![X0 : $i, X1 : $i]:
% 5.52/5.73         ((r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_A @ X0)) @ X0)
% 5.52/5.73          | (r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ X1)
% 5.52/5.73          | (r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_A @ X0)) @ sk_B))),
% 5.52/5.73      inference('sup-', [status(thm)], ['4', '43'])).
% 5.52/5.73  thf('45', plain,
% 5.52/5.73      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.52/5.73      inference('split', [status(esa)], ['9'])).
% 5.52/5.73  thf(l1_zfmisc_1, axiom,
% 5.52/5.73    (![A:$i,B:$i]:
% 5.52/5.73     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 5.52/5.73  thf('46', plain,
% 5.52/5.73      (![X10 : $i, X12 : $i]:
% 5.52/5.73         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 5.52/5.73      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 5.52/5.73  thf('47', plain,
% 5.52/5.73      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 5.52/5.73         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.52/5.73      inference('sup-', [status(thm)], ['45', '46'])).
% 5.52/5.73  thf('48', plain,
% 5.52/5.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.52/5.73         (~ (r2_hidden @ X0 @ X1)
% 5.52/5.73          | (r2_hidden @ X0 @ X2)
% 5.52/5.73          | ~ (r1_tarski @ X1 @ X2))),
% 5.52/5.73      inference('cnf', [status(esa)], [d3_tarski])).
% 5.52/5.73  thf('49', plain,
% 5.52/5.73      ((![X0 : $i]:
% 5.52/5.73          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 5.52/5.73         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.52/5.73      inference('sup-', [status(thm)], ['47', '48'])).
% 5.52/5.73  thf('50', plain, (((r2_hidden @ sk_A @ sk_B))),
% 5.52/5.73      inference('sat_resolution*', [status(thm)], ['14', '29', '30'])).
% 5.52/5.73  thf('51', plain,
% 5.52/5.73      (![X0 : $i]:
% 5.52/5.73         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 5.52/5.73      inference('simpl_trail', [status(thm)], ['49', '50'])).
% 5.52/5.73  thf('52', plain,
% 5.52/5.73      (![X0 : $i]:
% 5.52/5.73         ((r2_hidden @ 
% 5.52/5.73           (sk_C @ X0 @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A))) @ sk_B)
% 5.52/5.73          | (r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) @ X0)
% 5.52/5.73          | (r2_hidden @ 
% 5.52/5.73             (sk_C @ X0 @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A))) @ sk_B))),
% 5.52/5.73      inference('sup-', [status(thm)], ['44', '51'])).
% 5.52/5.73  thf(d1_ordinal1, axiom,
% 5.52/5.73    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 5.52/5.73  thf('53', plain,
% 5.52/5.73      (![X15 : $i]:
% 5.52/5.73         ((k1_ordinal1 @ X15) = (k2_xboole_0 @ X15 @ (k1_tarski @ X15)))),
% 5.52/5.73      inference('cnf', [status(esa)], [d1_ordinal1])).
% 5.52/5.73  thf('54', plain,
% 5.52/5.73      (![X15 : $i]:
% 5.52/5.73         ((k1_ordinal1 @ X15) = (k2_xboole_0 @ X15 @ (k1_tarski @ X15)))),
% 5.52/5.73      inference('cnf', [status(esa)], [d1_ordinal1])).
% 5.52/5.73  thf('55', plain,
% 5.52/5.73      (![X15 : $i]:
% 5.52/5.73         ((k1_ordinal1 @ X15) = (k2_xboole_0 @ X15 @ (k1_tarski @ X15)))),
% 5.52/5.73      inference('cnf', [status(esa)], [d1_ordinal1])).
% 5.52/5.73  thf('56', plain,
% 5.52/5.73      (![X0 : $i]:
% 5.52/5.73         ((r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ sk_A)) @ sk_B)
% 5.52/5.73          | (r1_tarski @ (k1_ordinal1 @ sk_A) @ X0)
% 5.52/5.73          | (r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ sk_A)) @ sk_B))),
% 5.52/5.73      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 5.52/5.73  thf('57', plain,
% 5.52/5.73      (![X0 : $i]:
% 5.52/5.73         ((r1_tarski @ (k1_ordinal1 @ sk_A) @ X0)
% 5.52/5.73          | (r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ sk_A)) @ sk_B))),
% 5.52/5.73      inference('simplify', [status(thm)], ['56'])).
% 5.52/5.73  thf('58', plain,
% 5.52/5.73      (![X1 : $i, X3 : $i]:
% 5.52/5.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.52/5.73      inference('cnf', [status(esa)], [d3_tarski])).
% 5.52/5.73  thf('59', plain,
% 5.52/5.73      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.52/5.73        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 5.52/5.73      inference('sup-', [status(thm)], ['57', '58'])).
% 5.52/5.73  thf('60', plain, ((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 5.52/5.73      inference('simplify', [status(thm)], ['59'])).
% 5.52/5.73  thf('61', plain,
% 5.52/5.73      (![X16 : $i, X17 : $i]:
% 5.52/5.73         (~ (v3_ordinal1 @ X16)
% 5.52/5.73          | ~ (v3_ordinal1 @ X17)
% 5.52/5.73          | (r1_ordinal1 @ X16 @ X17)
% 5.52/5.73          | ~ (r1_tarski @ X16 @ X17))),
% 5.52/5.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.52/5.73  thf('62', plain,
% 5.52/5.73      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.52/5.73        | ~ (v3_ordinal1 @ sk_B)
% 5.52/5.73        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 5.52/5.73      inference('sup-', [status(thm)], ['60', '61'])).
% 5.52/5.73  thf('63', plain, ((v3_ordinal1 @ sk_B)),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('64', plain,
% 5.52/5.73      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.52/5.73        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 5.52/5.73      inference('demod', [status(thm)], ['62', '63'])).
% 5.52/5.73  thf('65', plain,
% 5.52/5.73      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.52/5.73         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.52/5.73      inference('split', [status(esa)], ['13'])).
% 5.52/5.73  thf('66', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 5.52/5.73      inference('sat_resolution*', [status(thm)], ['14', '29'])).
% 5.52/5.73  thf('67', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 5.52/5.73      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 5.52/5.73  thf('68', plain, (~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))),
% 5.52/5.73      inference('clc', [status(thm)], ['64', '67'])).
% 5.52/5.73  thf('69', plain, (~ (v3_ordinal1 @ sk_A)),
% 5.52/5.73      inference('sup-', [status(thm)], ['0', '68'])).
% 5.52/5.73  thf('70', plain, ((v3_ordinal1 @ sk_A)),
% 5.52/5.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.52/5.73  thf('71', plain, ($false), inference('demod', [status(thm)], ['69', '70'])).
% 5.52/5.73  
% 5.52/5.73  % SZS output end Refutation
% 5.52/5.73  
% 5.57/5.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
