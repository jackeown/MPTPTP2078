%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BRwU0MPpRK

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:03 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 344 expanded)
%              Number of leaves         :   19 (  99 expanded)
%              Depth                    :   24
%              Number of atoms          :  622 (2892 expanded)
%              Number of equality atoms :   22 (  66 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('8',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( k1_ordinal1 @ X11 )
      = ( k2_xboole_0 @ X11 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('12',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_ordinal1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('15',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r2_hidden @ X16 @ X15 )
      | ( X16 = X15 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('27',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( sk_B = sk_A )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['11','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('31',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('34',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['10','35'])).

thf('37',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['9','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_ordinal1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['9','36'])).

thf('43',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('48',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('52',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('53',plain,
    ( ( sk_A = sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('56',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['10','35','55'])).

thf('57',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X11: $i] :
      ( ( k1_ordinal1 @ X11 )
      = ( k2_xboole_0 @ X11 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('59',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('60',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('64',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','64'])).

thf('66',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('68',plain,
    ( ( sk_A = sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['65','68'])).

thf('70',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['37','69'])).

thf('71',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','70'])).

thf('72',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BRwU0MPpRK
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.61  % Solved by: fo/fo7.sh
% 0.35/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.61  % done 269 iterations in 0.147s
% 0.35/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.61  % SZS output start Refutation
% 0.35/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.35/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.61  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.35/0.61  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.35/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.61  thf(t26_ordinal1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.35/0.61       ( ![B:$i]:
% 0.35/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.35/0.61           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.61  thf('0', plain,
% 0.35/0.61      (![X17 : $i, X18 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X17)
% 0.35/0.61          | (r1_ordinal1 @ X18 @ X17)
% 0.35/0.61          | (r2_hidden @ X17 @ X18)
% 0.35/0.61          | ~ (v3_ordinal1 @ X18))),
% 0.35/0.61      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.35/0.61  thf('1', plain,
% 0.35/0.61      (![X17 : $i, X18 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X17)
% 0.35/0.61          | (r1_ordinal1 @ X18 @ X17)
% 0.35/0.61          | (r2_hidden @ X17 @ X18)
% 0.35/0.61          | ~ (v3_ordinal1 @ X18))),
% 0.35/0.61      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.35/0.61  thf(antisymmetry_r2_hidden, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.35/0.61  thf('2', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.35/0.61      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.35/0.61  thf('3', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X0)
% 0.35/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.35/0.61          | ~ (v3_ordinal1 @ X1)
% 0.35/0.61          | ~ (r2_hidden @ X0 @ X1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.61  thf('4', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X0)
% 0.35/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.35/0.61          | ~ (v3_ordinal1 @ X1)
% 0.35/0.61          | ~ (v3_ordinal1 @ X0)
% 0.35/0.61          | (r1_ordinal1 @ X1 @ X0)
% 0.35/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['0', '3'])).
% 0.35/0.61  thf('5', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((r1_ordinal1 @ X1 @ X0)
% 0.35/0.61          | ~ (v3_ordinal1 @ X1)
% 0.35/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.35/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.35/0.61  thf('6', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.35/0.61      inference('eq_fact', [status(thm)], ['5'])).
% 0.35/0.61  thf('7', plain,
% 0.35/0.61      (![X0 : $i]: ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.35/0.61  thf(t34_ordinal1, conjecture,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.35/0.61       ( ![B:$i]:
% 0.35/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.35/0.61           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.35/0.61             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.61    (~( ![A:$i]:
% 0.35/0.61        ( ( v3_ordinal1 @ A ) =>
% 0.35/0.61          ( ![B:$i]:
% 0.35/0.61            ( ( v3_ordinal1 @ B ) =>
% 0.35/0.61              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.35/0.61                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.35/0.61    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.35/0.61  thf('8', plain,
% 0.35/0.61      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.35/0.61        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('9', plain,
% 0.35/0.61      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('split', [status(esa)], ['8'])).
% 0.35/0.61  thf('10', plain,
% 0.35/0.61      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.35/0.61       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.35/0.61      inference('split', [status(esa)], ['8'])).
% 0.35/0.61  thf(d1_ordinal1, axiom,
% 0.35/0.61    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.35/0.61  thf('11', plain,
% 0.35/0.61      (![X11 : $i]:
% 0.35/0.61         ((k1_ordinal1 @ X11) = (k2_xboole_0 @ X11 @ (k1_tarski @ X11)))),
% 0.35/0.61      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.35/0.61  thf('12', plain,
% 0.35/0.61      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('13', plain,
% 0.35/0.61      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('split', [status(esa)], ['12'])).
% 0.35/0.61  thf(redefinition_r1_ordinal1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.35/0.61       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.35/0.61  thf('14', plain,
% 0.35/0.61      (![X12 : $i, X13 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X12)
% 0.35/0.61          | ~ (v3_ordinal1 @ X13)
% 0.35/0.61          | (r1_tarski @ X12 @ X13)
% 0.35/0.61          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.35/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.35/0.61  thf('15', plain,
% 0.35/0.61      ((((r1_tarski @ sk_A @ sk_B)
% 0.35/0.61         | ~ (v3_ordinal1 @ sk_B)
% 0.35/0.61         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.61  thf('16', plain, ((v3_ordinal1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('17', plain, ((v3_ordinal1 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('18', plain,
% 0.35/0.61      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.35/0.61  thf(t24_ordinal1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.35/0.61       ( ![B:$i]:
% 0.35/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.35/0.61           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.35/0.61                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.35/0.61  thf('19', plain,
% 0.35/0.61      (![X15 : $i, X16 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X15)
% 0.35/0.61          | (r2_hidden @ X16 @ X15)
% 0.35/0.61          | ((X16) = (X15))
% 0.35/0.61          | (r2_hidden @ X15 @ X16)
% 0.35/0.61          | ~ (v3_ordinal1 @ X16))),
% 0.35/0.61      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.35/0.61  thf(t7_ordinal1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.61  thf('20', plain,
% 0.35/0.61      (![X19 : $i, X20 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.35/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.61  thf('21', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X1)
% 0.35/0.61          | (r2_hidden @ X0 @ X1)
% 0.35/0.61          | ((X1) = (X0))
% 0.35/0.61          | ~ (v3_ordinal1 @ X0)
% 0.35/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.61  thf('22', plain,
% 0.35/0.61      (((~ (v3_ordinal1 @ sk_A)
% 0.35/0.61         | ((sk_B) = (sk_A))
% 0.35/0.61         | (r2_hidden @ sk_A @ sk_B)
% 0.35/0.61         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['18', '21'])).
% 0.35/0.61  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('24', plain, ((v3_ordinal1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('25', plain,
% 0.35/0.61      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.35/0.61         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.35/0.61  thf(d3_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.35/0.61       ( ![D:$i]:
% 0.35/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.61           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.61  thf('26', plain,
% 0.35/0.61      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X2 @ X5)
% 0.35/0.61          | (r2_hidden @ X2 @ X4)
% 0.35/0.61          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.61  thf('27', plain,
% 0.35/0.61      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.35/0.61         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.35/0.61      inference('simplify', [status(thm)], ['26'])).
% 0.35/0.61  thf('28', plain,
% 0.35/0.61      ((![X0 : $i]:
% 0.35/0.61          (((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.35/0.61         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['25', '27'])).
% 0.35/0.61  thf('29', plain,
% 0.35/0.61      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)) | ((sk_B) = (sk_A))))
% 0.35/0.61         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['11', '28'])).
% 0.35/0.61  thf('30', plain,
% 0.35/0.61      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.35/0.61         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.61      inference('split', [status(esa)], ['8'])).
% 0.35/0.61  thf('31', plain,
% 0.35/0.61      ((((sk_B) = (sk_A)))
% 0.35/0.61         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.35/0.61             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.61  thf('32', plain,
% 0.35/0.61      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.35/0.61         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.61      inference('split', [status(esa)], ['8'])).
% 0.35/0.61  thf('33', plain,
% 0.35/0.61      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.35/0.61         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.35/0.61             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.61  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.35/0.61  thf('34', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_ordinal1 @ X14))),
% 0.35/0.61      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.35/0.61  thf('35', plain,
% 0.35/0.61      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.35/0.61       ~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.61  thf('36', plain, (~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.35/0.61      inference('sat_resolution*', [status(thm)], ['10', '35'])).
% 0.35/0.61  thf('37', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.35/0.61      inference('simpl_trail', [status(thm)], ['9', '36'])).
% 0.35/0.61  thf('38', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((r1_ordinal1 @ X1 @ X0)
% 0.35/0.61          | ~ (v3_ordinal1 @ X1)
% 0.35/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.35/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.35/0.61  thf('39', plain,
% 0.35/0.61      (![X12 : $i, X13 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X12)
% 0.35/0.61          | ~ (v3_ordinal1 @ X13)
% 0.35/0.61          | (r1_tarski @ X12 @ X13)
% 0.35/0.61          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.35/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.35/0.61  thf('40', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X0)
% 0.35/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.35/0.61          | ~ (v3_ordinal1 @ X1)
% 0.35/0.61          | (r1_tarski @ X1 @ X0)
% 0.35/0.61          | ~ (v3_ordinal1 @ X0)
% 0.35/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.35/0.61  thf('41', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((r1_tarski @ X1 @ X0)
% 0.35/0.61          | ~ (v3_ordinal1 @ X1)
% 0.35/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.35/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.35/0.61      inference('simplify', [status(thm)], ['40'])).
% 0.35/0.61  thf('42', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.35/0.61      inference('simpl_trail', [status(thm)], ['9', '36'])).
% 0.35/0.61  thf('43', plain,
% 0.35/0.61      ((~ (v3_ordinal1 @ sk_A)
% 0.35/0.61        | ~ (v3_ordinal1 @ sk_B)
% 0.35/0.61        | (r1_tarski @ sk_B @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.35/0.61  thf('44', plain, ((v3_ordinal1 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('45', plain, ((v3_ordinal1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('46', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.35/0.61      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.35/0.61  thf('47', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (~ (v3_ordinal1 @ X1)
% 0.35/0.61          | (r2_hidden @ X0 @ X1)
% 0.35/0.61          | ((X1) = (X0))
% 0.35/0.61          | ~ (v3_ordinal1 @ X0)
% 0.35/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.61  thf('48', plain,
% 0.35/0.61      ((~ (v3_ordinal1 @ sk_B)
% 0.35/0.61        | ((sk_A) = (sk_B))
% 0.35/0.61        | (r2_hidden @ sk_B @ sk_A)
% 0.35/0.61        | ~ (v3_ordinal1 @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.61  thf('49', plain, ((v3_ordinal1 @ sk_B)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('51', plain, ((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_A))),
% 0.35/0.61      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.35/0.61  thf(l1_zfmisc_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.35/0.61  thf('52', plain,
% 0.35/0.61      (![X8 : $i, X10 : $i]:
% 0.35/0.61         ((r1_tarski @ (k1_tarski @ X8) @ X10) | ~ (r2_hidden @ X8 @ X10))),
% 0.35/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.35/0.61  thf('53', plain,
% 0.35/0.61      ((((sk_A) = (sk_B)) | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.35/0.61  thf('54', plain,
% 0.35/0.61      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.35/0.61         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.35/0.61      inference('split', [status(esa)], ['12'])).
% 0.35/0.61  thf('55', plain,
% 0.35/0.61      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.35/0.61       ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.35/0.61      inference('split', [status(esa)], ['12'])).
% 0.35/0.61  thf('56', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.35/0.61      inference('sat_resolution*', [status(thm)], ['10', '35', '55'])).
% 0.35/0.61  thf('57', plain, ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))),
% 0.35/0.61      inference('simpl_trail', [status(thm)], ['54', '56'])).
% 0.35/0.61  thf('58', plain,
% 0.35/0.61      (![X11 : $i]:
% 0.35/0.61         ((k1_ordinal1 @ X11) = (k2_xboole_0 @ X11 @ (k1_tarski @ X11)))),
% 0.35/0.61      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.35/0.61  thf('59', plain,
% 0.35/0.61      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X6 @ X4)
% 0.35/0.61          | (r2_hidden @ X6 @ X5)
% 0.35/0.61          | (r2_hidden @ X6 @ X3)
% 0.35/0.61          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.61      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.61  thf('60', plain,
% 0.35/0.61      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.35/0.61         ((r2_hidden @ X6 @ X3)
% 0.35/0.61          | (r2_hidden @ X6 @ X5)
% 0.35/0.61          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['59'])).
% 0.35/0.61  thf('61', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.35/0.61          | (r2_hidden @ X1 @ X0)
% 0.35/0.61          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['58', '60'])).
% 0.35/0.61  thf('62', plain,
% 0.35/0.61      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['57', '61'])).
% 0.35/0.61  thf('63', plain,
% 0.35/0.61      (![X19 : $i, X20 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.35/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.61  thf('64', plain,
% 0.35/0.61      (((r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.35/0.61  thf('65', plain, ((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['53', '64'])).
% 0.35/0.61  thf('66', plain, ((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_A))),
% 0.35/0.61      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.35/0.61  thf('67', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.35/0.61      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.35/0.61  thf('68', plain, ((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.35/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.35/0.61  thf('69', plain, (((sk_A) = (sk_B))),
% 0.35/0.61      inference('clc', [status(thm)], ['65', '68'])).
% 0.35/0.61  thf('70', plain, (~ (r1_ordinal1 @ sk_A @ sk_A)),
% 0.35/0.61      inference('demod', [status(thm)], ['37', '69'])).
% 0.35/0.61  thf('71', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.35/0.61      inference('sup-', [status(thm)], ['7', '70'])).
% 0.35/0.61  thf('72', plain, ((v3_ordinal1 @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('73', plain, ($false), inference('demod', [status(thm)], ['71', '72'])).
% 0.35/0.61  
% 0.35/0.61  % SZS output end Refutation
% 0.35/0.61  
% 0.35/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
