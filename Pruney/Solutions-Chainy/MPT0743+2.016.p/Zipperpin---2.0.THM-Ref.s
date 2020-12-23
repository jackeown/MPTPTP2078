%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kC06SapHxf

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:54 EST 2020

% Result     : Theorem 9.10s
% Output     : Refutation 9.10s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 244 expanded)
%              Number of leaves         :   19 (  74 expanded)
%              Depth                    :   23
%              Number of atoms          :  670 (1948 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ( r1_ordinal1 @ X20 @ X19 )
      | ( r2_hidden @ X19 @ X20 )
      | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

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

thf('6',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('15',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('23',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('24',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k1_tarski @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k2_xboole_0 @ X9 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X21: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X21 ) )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('35',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('37',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('49',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['22','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['20','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('53',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('54',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['22','47','48'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) ) @ sk_B )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('61',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('62',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_ordinal1 @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('69',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('73',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['22','47'])).

thf('74',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['71','74'])).

thf('76',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','75'])).

thf('77',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kC06SapHxf
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 9.10/9.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.10/9.28  % Solved by: fo/fo7.sh
% 9.10/9.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.10/9.28  % done 9179 iterations in 8.822s
% 9.10/9.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.10/9.28  % SZS output start Refutation
% 9.10/9.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.10/9.28  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 9.10/9.28  thf(sk_B_type, type, sk_B: $i).
% 9.10/9.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 9.10/9.28  thf(sk_A_type, type, sk_A: $i).
% 9.10/9.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.10/9.28  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 9.10/9.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 9.10/9.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.10/9.28  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 9.10/9.28  thf(t29_ordinal1, axiom,
% 9.10/9.28    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 9.10/9.28  thf('0', plain,
% 9.10/9.28      (![X21 : $i]:
% 9.10/9.28         ((v3_ordinal1 @ (k1_ordinal1 @ X21)) | ~ (v3_ordinal1 @ X21))),
% 9.10/9.28      inference('cnf', [status(esa)], [t29_ordinal1])).
% 9.10/9.28  thf(d3_tarski, axiom,
% 9.10/9.28    (![A:$i,B:$i]:
% 9.10/9.28     ( ( r1_tarski @ A @ B ) <=>
% 9.10/9.28       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 9.10/9.28  thf('1', plain,
% 9.10/9.28      (![X3 : $i, X5 : $i]:
% 9.10/9.28         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 9.10/9.28      inference('cnf', [status(esa)], [d3_tarski])).
% 9.10/9.28  thf(d3_xboole_0, axiom,
% 9.10/9.28    (![A:$i,B:$i,C:$i]:
% 9.10/9.28     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 9.10/9.28       ( ![D:$i]:
% 9.10/9.28         ( ( r2_hidden @ D @ C ) <=>
% 9.10/9.28           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 9.10/9.28  thf('2', plain,
% 9.10/9.28      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 9.10/9.28         (~ (r2_hidden @ X10 @ X8)
% 9.10/9.28          | (r2_hidden @ X10 @ X9)
% 9.10/9.28          | (r2_hidden @ X10 @ X7)
% 9.10/9.28          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 9.10/9.28      inference('cnf', [status(esa)], [d3_xboole_0])).
% 9.10/9.28  thf('3', plain,
% 9.10/9.28      (![X7 : $i, X9 : $i, X10 : $i]:
% 9.10/9.28         ((r2_hidden @ X10 @ X7)
% 9.10/9.28          | (r2_hidden @ X10 @ X9)
% 9.10/9.28          | ~ (r2_hidden @ X10 @ (k2_xboole_0 @ X9 @ X7)))),
% 9.10/9.28      inference('simplify', [status(thm)], ['2'])).
% 9.10/9.28  thf('4', plain,
% 9.10/9.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.10/9.28         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 9.10/9.28          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 9.10/9.28          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 9.10/9.28      inference('sup-', [status(thm)], ['1', '3'])).
% 9.10/9.28  thf(t26_ordinal1, axiom,
% 9.10/9.28    (![A:$i]:
% 9.10/9.28     ( ( v3_ordinal1 @ A ) =>
% 9.10/9.28       ( ![B:$i]:
% 9.10/9.28         ( ( v3_ordinal1 @ B ) =>
% 9.10/9.28           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 9.10/9.28  thf('5', plain,
% 9.10/9.28      (![X19 : $i, X20 : $i]:
% 9.10/9.28         (~ (v3_ordinal1 @ X19)
% 9.10/9.28          | (r1_ordinal1 @ X20 @ X19)
% 9.10/9.28          | (r2_hidden @ X19 @ X20)
% 9.10/9.28          | ~ (v3_ordinal1 @ X20))),
% 9.10/9.28      inference('cnf', [status(esa)], [t26_ordinal1])).
% 9.10/9.28  thf(t33_ordinal1, conjecture,
% 9.10/9.28    (![A:$i]:
% 9.10/9.28     ( ( v3_ordinal1 @ A ) =>
% 9.10/9.28       ( ![B:$i]:
% 9.10/9.28         ( ( v3_ordinal1 @ B ) =>
% 9.10/9.28           ( ( r2_hidden @ A @ B ) <=>
% 9.10/9.28             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 9.10/9.28  thf(zf_stmt_0, negated_conjecture,
% 9.10/9.28    (~( ![A:$i]:
% 9.10/9.28        ( ( v3_ordinal1 @ A ) =>
% 9.10/9.28          ( ![B:$i]:
% 9.10/9.28            ( ( v3_ordinal1 @ B ) =>
% 9.10/9.28              ( ( r2_hidden @ A @ B ) <=>
% 9.10/9.28                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 9.10/9.28    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 9.10/9.28  thf('6', plain,
% 9.10/9.28      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('7', plain,
% 9.10/9.28      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('split', [status(esa)], ['6'])).
% 9.10/9.28  thf(antisymmetry_r2_hidden, axiom,
% 9.10/9.28    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 9.10/9.28  thf('8', plain,
% 9.10/9.28      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 9.10/9.28      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 9.10/9.28  thf('9', plain,
% 9.10/9.28      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['7', '8'])).
% 9.10/9.28  thf('10', plain,
% 9.10/9.28      (((~ (v3_ordinal1 @ sk_A)
% 9.10/9.28         | (r1_ordinal1 @ sk_A @ sk_B)
% 9.10/9.28         | ~ (v3_ordinal1 @ sk_B))) <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['5', '9'])).
% 9.10/9.28  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('13', plain,
% 9.10/9.28      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('demod', [status(thm)], ['10', '11', '12'])).
% 9.10/9.28  thf(redefinition_r1_ordinal1, axiom,
% 9.10/9.28    (![A:$i,B:$i]:
% 9.10/9.28     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 9.10/9.28       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 9.10/9.28  thf('14', plain,
% 9.10/9.28      (![X17 : $i, X18 : $i]:
% 9.10/9.28         (~ (v3_ordinal1 @ X17)
% 9.10/9.28          | ~ (v3_ordinal1 @ X18)
% 9.10/9.28          | (r1_tarski @ X17 @ X18)
% 9.10/9.28          | ~ (r1_ordinal1 @ X17 @ X18))),
% 9.10/9.28      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 9.10/9.28  thf('15', plain,
% 9.10/9.28      ((((r1_tarski @ sk_A @ sk_B)
% 9.10/9.28         | ~ (v3_ordinal1 @ sk_B)
% 9.10/9.28         | ~ (v3_ordinal1 @ sk_A))) <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['13', '14'])).
% 9.10/9.28  thf('16', plain, ((v3_ordinal1 @ sk_B)),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('17', plain, ((v3_ordinal1 @ sk_A)),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('18', plain,
% 9.10/9.28      (((r1_tarski @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('demod', [status(thm)], ['15', '16', '17'])).
% 9.10/9.28  thf('19', plain,
% 9.10/9.28      (![X2 : $i, X3 : $i, X4 : $i]:
% 9.10/9.28         (~ (r2_hidden @ X2 @ X3)
% 9.10/9.28          | (r2_hidden @ X2 @ X4)
% 9.10/9.28          | ~ (r1_tarski @ X3 @ X4))),
% 9.10/9.28      inference('cnf', [status(esa)], [d3_tarski])).
% 9.10/9.28  thf('20', plain,
% 9.10/9.28      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A)))
% 9.10/9.28         <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['18', '19'])).
% 9.10/9.28  thf('21', plain,
% 9.10/9.28      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 9.10/9.28        | ~ (r2_hidden @ sk_A @ sk_B))),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('22', plain,
% 9.10/9.28      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 9.10/9.28       ~ ((r2_hidden @ sk_A @ sk_B))),
% 9.10/9.28      inference('split', [status(esa)], ['21'])).
% 9.10/9.28  thf(d1_ordinal1, axiom,
% 9.10/9.28    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 9.10/9.28  thf('23', plain,
% 9.10/9.28      (![X16 : $i]:
% 9.10/9.28         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 9.10/9.28      inference('cnf', [status(esa)], [d1_ordinal1])).
% 9.10/9.28  thf('24', plain,
% 9.10/9.28      (![X3 : $i, X5 : $i]:
% 9.10/9.28         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 9.10/9.28      inference('cnf', [status(esa)], [d3_tarski])).
% 9.10/9.28  thf('25', plain,
% 9.10/9.28      (![X3 : $i, X5 : $i]:
% 9.10/9.28         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 9.10/9.28      inference('cnf', [status(esa)], [d3_tarski])).
% 9.10/9.28  thf('26', plain,
% 9.10/9.28      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 9.10/9.28      inference('sup-', [status(thm)], ['24', '25'])).
% 9.10/9.28  thf('27', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.10/9.28      inference('simplify', [status(thm)], ['26'])).
% 9.10/9.28  thf(l1_zfmisc_1, axiom,
% 9.10/9.28    (![A:$i,B:$i]:
% 9.10/9.28     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 9.10/9.28  thf('28', plain,
% 9.10/9.28      (![X13 : $i, X14 : $i]:
% 9.10/9.28         ((r2_hidden @ X13 @ X14) | ~ (r1_tarski @ (k1_tarski @ X13) @ X14))),
% 9.10/9.28      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 9.10/9.28  thf('29', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 9.10/9.28      inference('sup-', [status(thm)], ['27', '28'])).
% 9.10/9.28  thf('30', plain,
% 9.10/9.28      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 9.10/9.28         (~ (r2_hidden @ X6 @ X7)
% 9.10/9.28          | (r2_hidden @ X6 @ X8)
% 9.10/9.28          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 9.10/9.28      inference('cnf', [status(esa)], [d3_xboole_0])).
% 9.10/9.28  thf('31', plain,
% 9.10/9.28      (![X6 : $i, X7 : $i, X9 : $i]:
% 9.10/9.28         ((r2_hidden @ X6 @ (k2_xboole_0 @ X9 @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 9.10/9.28      inference('simplify', [status(thm)], ['30'])).
% 9.10/9.28  thf('32', plain,
% 9.10/9.28      (![X0 : $i, X1 : $i]:
% 9.10/9.28         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['29', '31'])).
% 9.10/9.28  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 9.10/9.28      inference('sup+', [status(thm)], ['23', '32'])).
% 9.10/9.28  thf('34', plain,
% 9.10/9.28      (![X21 : $i]:
% 9.10/9.28         ((v3_ordinal1 @ (k1_ordinal1 @ X21)) | ~ (v3_ordinal1 @ X21))),
% 9.10/9.28      inference('cnf', [status(esa)], [t29_ordinal1])).
% 9.10/9.28  thf('35', plain,
% 9.10/9.28      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 9.10/9.28         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 9.10/9.28      inference('split', [status(esa)], ['6'])).
% 9.10/9.28  thf('36', plain,
% 9.10/9.28      (![X17 : $i, X18 : $i]:
% 9.10/9.28         (~ (v3_ordinal1 @ X17)
% 9.10/9.28          | ~ (v3_ordinal1 @ X18)
% 9.10/9.28          | (r1_tarski @ X17 @ X18)
% 9.10/9.28          | ~ (r1_ordinal1 @ X17 @ X18))),
% 9.10/9.28      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 9.10/9.28  thf('37', plain,
% 9.10/9.28      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 9.10/9.28         | ~ (v3_ordinal1 @ sk_B)
% 9.10/9.28         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 9.10/9.28         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['35', '36'])).
% 9.10/9.28  thf('38', plain, ((v3_ordinal1 @ sk_B)),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('39', plain,
% 9.10/9.28      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 9.10/9.28         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 9.10/9.28         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 9.10/9.28      inference('demod', [status(thm)], ['37', '38'])).
% 9.10/9.28  thf('40', plain,
% 9.10/9.28      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 9.10/9.28         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['34', '39'])).
% 9.10/9.28  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('42', plain,
% 9.10/9.28      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 9.10/9.28         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 9.10/9.28      inference('demod', [status(thm)], ['40', '41'])).
% 9.10/9.28  thf('43', plain,
% 9.10/9.28      (![X2 : $i, X3 : $i, X4 : $i]:
% 9.10/9.28         (~ (r2_hidden @ X2 @ X3)
% 9.10/9.28          | (r2_hidden @ X2 @ X4)
% 9.10/9.28          | ~ (r1_tarski @ X3 @ X4))),
% 9.10/9.28      inference('cnf', [status(esa)], [d3_tarski])).
% 9.10/9.28  thf('44', plain,
% 9.10/9.28      ((![X0 : $i]:
% 9.10/9.28          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 9.10/9.28         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['42', '43'])).
% 9.10/9.28  thf('45', plain,
% 9.10/9.28      (((r2_hidden @ sk_A @ sk_B))
% 9.10/9.28         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['33', '44'])).
% 9.10/9.28  thf('46', plain,
% 9.10/9.28      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('split', [status(esa)], ['21'])).
% 9.10/9.28  thf('47', plain,
% 9.10/9.28      (((r2_hidden @ sk_A @ sk_B)) | 
% 9.10/9.28       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 9.10/9.28      inference('sup-', [status(thm)], ['45', '46'])).
% 9.10/9.28  thf('48', plain,
% 9.10/9.28      (((r2_hidden @ sk_A @ sk_B)) | 
% 9.10/9.28       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 9.10/9.28      inference('split', [status(esa)], ['6'])).
% 9.10/9.28  thf('49', plain, (((r2_hidden @ sk_A @ sk_B))),
% 9.10/9.28      inference('sat_resolution*', [status(thm)], ['22', '47', '48'])).
% 9.10/9.28  thf('50', plain,
% 9.10/9.28      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 9.10/9.28      inference('simpl_trail', [status(thm)], ['20', '49'])).
% 9.10/9.28  thf('51', plain,
% 9.10/9.28      (![X0 : $i, X1 : $i]:
% 9.10/9.28         ((r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_A @ X0)) @ X0)
% 9.10/9.28          | (r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ X1)
% 9.10/9.28          | (r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_A @ X0)) @ sk_B))),
% 9.10/9.28      inference('sup-', [status(thm)], ['4', '50'])).
% 9.10/9.28  thf('52', plain,
% 9.10/9.28      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('split', [status(esa)], ['6'])).
% 9.10/9.28  thf('53', plain,
% 9.10/9.28      (![X13 : $i, X15 : $i]:
% 9.10/9.28         ((r1_tarski @ (k1_tarski @ X13) @ X15) | ~ (r2_hidden @ X13 @ X15))),
% 9.10/9.28      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 9.10/9.28  thf('54', plain,
% 9.10/9.28      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 9.10/9.28         <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['52', '53'])).
% 9.10/9.28  thf('55', plain,
% 9.10/9.28      (![X2 : $i, X3 : $i, X4 : $i]:
% 9.10/9.28         (~ (r2_hidden @ X2 @ X3)
% 9.10/9.28          | (r2_hidden @ X2 @ X4)
% 9.10/9.28          | ~ (r1_tarski @ X3 @ X4))),
% 9.10/9.28      inference('cnf', [status(esa)], [d3_tarski])).
% 9.10/9.28  thf('56', plain,
% 9.10/9.28      ((![X0 : $i]:
% 9.10/9.28          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 9.10/9.28         <= (((r2_hidden @ sk_A @ sk_B)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['54', '55'])).
% 9.10/9.28  thf('57', plain, (((r2_hidden @ sk_A @ sk_B))),
% 9.10/9.28      inference('sat_resolution*', [status(thm)], ['22', '47', '48'])).
% 9.10/9.28  thf('58', plain,
% 9.10/9.28      (![X0 : $i]:
% 9.10/9.28         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 9.10/9.28      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 9.10/9.28  thf('59', plain,
% 9.10/9.28      (![X0 : $i]:
% 9.10/9.28         ((r2_hidden @ 
% 9.10/9.28           (sk_C @ X0 @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A))) @ sk_B)
% 9.10/9.28          | (r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) @ X0)
% 9.10/9.28          | (r2_hidden @ 
% 9.10/9.28             (sk_C @ X0 @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A))) @ sk_B))),
% 9.10/9.28      inference('sup-', [status(thm)], ['51', '58'])).
% 9.10/9.28  thf('60', plain,
% 9.10/9.28      (![X16 : $i]:
% 9.10/9.28         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 9.10/9.28      inference('cnf', [status(esa)], [d1_ordinal1])).
% 9.10/9.28  thf('61', plain,
% 9.10/9.28      (![X16 : $i]:
% 9.10/9.28         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 9.10/9.28      inference('cnf', [status(esa)], [d1_ordinal1])).
% 9.10/9.28  thf('62', plain,
% 9.10/9.28      (![X16 : $i]:
% 9.10/9.28         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 9.10/9.28      inference('cnf', [status(esa)], [d1_ordinal1])).
% 9.10/9.28  thf('63', plain,
% 9.10/9.28      (![X0 : $i]:
% 9.10/9.28         ((r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ sk_A)) @ sk_B)
% 9.10/9.28          | (r1_tarski @ (k1_ordinal1 @ sk_A) @ X0)
% 9.10/9.28          | (r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ sk_A)) @ sk_B))),
% 9.10/9.28      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 9.10/9.28  thf('64', plain,
% 9.10/9.28      (![X0 : $i]:
% 9.10/9.28         ((r1_tarski @ (k1_ordinal1 @ sk_A) @ X0)
% 9.10/9.28          | (r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ sk_A)) @ sk_B))),
% 9.10/9.28      inference('simplify', [status(thm)], ['63'])).
% 9.10/9.28  thf('65', plain,
% 9.10/9.28      (![X3 : $i, X5 : $i]:
% 9.10/9.28         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 9.10/9.28      inference('cnf', [status(esa)], [d3_tarski])).
% 9.10/9.28  thf('66', plain,
% 9.10/9.28      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 9.10/9.28        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 9.10/9.28      inference('sup-', [status(thm)], ['64', '65'])).
% 9.10/9.28  thf('67', plain, ((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 9.10/9.28      inference('simplify', [status(thm)], ['66'])).
% 9.10/9.28  thf('68', plain,
% 9.10/9.28      (![X17 : $i, X18 : $i]:
% 9.10/9.28         (~ (v3_ordinal1 @ X17)
% 9.10/9.28          | ~ (v3_ordinal1 @ X18)
% 9.10/9.28          | (r1_ordinal1 @ X17 @ X18)
% 9.10/9.28          | ~ (r1_tarski @ X17 @ X18))),
% 9.10/9.28      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 9.10/9.28  thf('69', plain,
% 9.10/9.28      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 9.10/9.28        | ~ (v3_ordinal1 @ sk_B)
% 9.10/9.28        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 9.10/9.28      inference('sup-', [status(thm)], ['67', '68'])).
% 9.10/9.28  thf('70', plain, ((v3_ordinal1 @ sk_B)),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('71', plain,
% 9.10/9.28      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 9.10/9.28        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 9.10/9.28      inference('demod', [status(thm)], ['69', '70'])).
% 9.10/9.28  thf('72', plain,
% 9.10/9.28      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 9.10/9.28         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 9.10/9.28      inference('split', [status(esa)], ['21'])).
% 9.10/9.28  thf('73', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 9.10/9.28      inference('sat_resolution*', [status(thm)], ['22', '47'])).
% 9.10/9.28  thf('74', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 9.10/9.28      inference('simpl_trail', [status(thm)], ['72', '73'])).
% 9.10/9.28  thf('75', plain, (~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))),
% 9.10/9.28      inference('clc', [status(thm)], ['71', '74'])).
% 9.10/9.28  thf('76', plain, (~ (v3_ordinal1 @ sk_A)),
% 9.10/9.28      inference('sup-', [status(thm)], ['0', '75'])).
% 9.10/9.28  thf('77', plain, ((v3_ordinal1 @ sk_A)),
% 9.10/9.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.10/9.28  thf('78', plain, ($false), inference('demod', [status(thm)], ['76', '77'])).
% 9.10/9.28  
% 9.10/9.28  % SZS output end Refutation
% 9.10/9.28  
% 9.10/9.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
