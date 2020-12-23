%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TD3PSxTFbD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:29 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 405 expanded)
%              Number of leaves         :   28 ( 119 expanded)
%              Depth                    :   22
%              Number of atoms          :  962 (4933 expanded)
%              Number of equality atoms :  176 (1038 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X57: $i,X58: $i] :
      ( ( X58
        = ( k1_tarski @ X57 ) )
      | ( X58 = k1_xboole_0 )
      | ~ ( r1_tarski @ X58 @ ( k1_tarski @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','22'])).

thf('24',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( r1_xboole_0 @ X19 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('26',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k2_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('47',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('53',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','49'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B
      = ( k5_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( sk_B
      = ( k5_xboole_0 @ sk_C_2 @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('68',plain,
    ( ( sk_B = sk_C_2 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B )
    | ( sk_B = sk_C_2 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('71',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('72',plain,
    ( ( sk_C_2 != sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('78',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('82',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','80','83'])).

thf('85',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','84'])).

thf('86',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('92',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('95',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['87','95'])).

thf('97',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['86','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','97'])).

thf('99',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['24','98'])).

thf('100',plain,(
    $false ),
    inference(simplify,[status(thm)],['99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TD3PSxTFbD
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.06  % Solved by: fo/fo7.sh
% 0.84/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.06  % done 1340 iterations in 0.606s
% 0.84/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.06  % SZS output start Refutation
% 0.84/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.84/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.84/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.06  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.84/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(t43_zfmisc_1, conjecture,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.84/1.06          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.84/1.06          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.84/1.06          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.84/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.06        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.84/1.06             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.84/1.06             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.84/1.06             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.84/1.06    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.84/1.06  thf('0', plain,
% 0.84/1.06      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('1', plain,
% 0.84/1.06      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.84/1.06         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('3', plain,
% 0.84/1.06      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.84/1.06         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('demod', [status(thm)], ['1', '2'])).
% 0.84/1.06  thf('4', plain,
% 0.84/1.06      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf('5', plain,
% 0.84/1.06      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('6', plain,
% 0.84/1.06      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.84/1.06      inference('split', [status(esa)], ['5'])).
% 0.84/1.06  thf(t7_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.06  thf('7', plain,
% 0.84/1.06      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.84/1.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.06  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(l3_zfmisc_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.84/1.06       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.84/1.06  thf('9', plain,
% 0.84/1.06      (![X57 : $i, X58 : $i]:
% 0.84/1.06         (((X58) = (k1_tarski @ X57))
% 0.84/1.06          | ((X58) = (k1_xboole_0))
% 0.84/1.06          | ~ (r1_tarski @ X58 @ (k1_tarski @ X57)))),
% 0.84/1.06      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.84/1.06  thf('10', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.84/1.06          | ((X0) = (k1_xboole_0))
% 0.84/1.06          | ((X0) = (k1_tarski @ sk_A)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['8', '9'])).
% 0.84/1.06  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('12', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.84/1.06          | ((X0) = (k1_xboole_0))
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.84/1.06      inference('demod', [status(thm)], ['10', '11'])).
% 0.84/1.06  thf('13', plain,
% 0.84/1.06      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['7', '12'])).
% 0.84/1.06  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('15', plain,
% 0.84/1.06      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('16', plain,
% 0.84/1.06      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('split', [status(esa)], ['15'])).
% 0.84/1.06  thf('17', plain,
% 0.84/1.06      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.84/1.06         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['14', '16'])).
% 0.84/1.06  thf('18', plain,
% 0.84/1.06      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.84/1.06         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['13', '17'])).
% 0.84/1.06  thf('19', plain,
% 0.84/1.06      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('simplify', [status(thm)], ['18'])).
% 0.84/1.06  thf('20', plain,
% 0.84/1.06      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.84/1.06      inference('split', [status(esa)], ['0'])).
% 0.84/1.06  thf('21', plain,
% 0.84/1.06      ((((sk_B) != (sk_B)))
% 0.84/1.06         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['19', '20'])).
% 0.84/1.06  thf('22', plain,
% 0.84/1.06      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['21'])).
% 0.84/1.06  thf('23', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.84/1.06      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 0.84/1.06  thf('24', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.84/1.06      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.84/1.06  thf(t66_xboole_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.84/1.06       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.84/1.06  thf('25', plain,
% 0.84/1.06      (![X19 : $i]: ((r1_xboole_0 @ X19 @ X19) | ((X19) != (k1_xboole_0)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.84/1.06  thf('26', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.84/1.06      inference('simplify', [status(thm)], ['25'])).
% 0.84/1.06  thf(d3_tarski, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( r1_tarski @ A @ B ) <=>
% 0.84/1.06       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.84/1.06  thf('27', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i]:
% 0.84/1.06         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.06  thf('28', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i]:
% 0.84/1.06         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.06  thf(t3_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.84/1.06            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.06       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.84/1.06            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.84/1.06  thf('29', plain,
% 0.84/1.06      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X10 @ X8)
% 0.84/1.06          | ~ (r2_hidden @ X10 @ X11)
% 0.84/1.06          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.06  thf('30', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         ((r1_tarski @ X0 @ X1)
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.84/1.06          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.84/1.06      inference('sup-', [status(thm)], ['28', '29'])).
% 0.84/1.06  thf('31', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((r1_tarski @ X0 @ X1)
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.84/1.06          | (r1_tarski @ X0 @ X1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['27', '30'])).
% 0.84/1.06  thf('32', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.84/1.06      inference('simplify', [status(thm)], ['31'])).
% 0.84/1.06  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.84/1.06      inference('sup-', [status(thm)], ['26', '32'])).
% 0.84/1.06  thf(t12_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.84/1.06  thf('34', plain,
% 0.84/1.06      (![X14 : $i, X15 : $i]:
% 0.84/1.06         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.84/1.06      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.84/1.06  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.06  thf('36', plain,
% 0.84/1.06      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['7', '12'])).
% 0.84/1.06  thf(t95_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( k3_xboole_0 @ A @ B ) =
% 0.84/1.06       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.84/1.06  thf('37', plain,
% 0.84/1.06      (![X27 : $i, X28 : $i]:
% 0.84/1.06         ((k3_xboole_0 @ X27 @ X28)
% 0.84/1.06           = (k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ 
% 0.84/1.06              (k2_xboole_0 @ X27 @ X28)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.84/1.06  thf(t91_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.84/1.06       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.84/1.06  thf('38', plain,
% 0.84/1.06      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.06         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.84/1.06           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.84/1.06  thf('39', plain,
% 0.84/1.06      (![X27 : $i, X28 : $i]:
% 0.84/1.06         ((k3_xboole_0 @ X27 @ X28)
% 0.84/1.06           = (k5_xboole_0 @ X27 @ 
% 0.84/1.06              (k5_xboole_0 @ X28 @ (k2_xboole_0 @ X27 @ X28))))),
% 0.84/1.06      inference('demod', [status(thm)], ['37', '38'])).
% 0.84/1.06  thf('40', plain,
% 0.84/1.06      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 0.84/1.06          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ sk_B)))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['36', '39'])).
% 0.84/1.06  thf(commutativity_k5_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.84/1.06  thf('41', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf('42', plain,
% 0.84/1.06      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 0.84/1.06          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C_2)))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['40', '41'])).
% 0.84/1.06  thf(t92_xboole_1, axiom,
% 0.84/1.06    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.84/1.06  thf('43', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.84/1.06      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.84/1.06  thf('44', plain,
% 0.84/1.06      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.06         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.84/1.06           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.84/1.06  thf('45', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.84/1.06           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['43', '44'])).
% 0.84/1.06  thf('46', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf(t5_boole, axiom,
% 0.84/1.06    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.84/1.06  thf('47', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.84/1.06      inference('cnf', [status(esa)], [t5_boole])).
% 0.84/1.06  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.84/1.06      inference('sup+', [status(thm)], ['46', '47'])).
% 0.84/1.06  thf('49', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['45', '48'])).
% 0.84/1.06  thf('50', plain,
% 0.84/1.06      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['42', '49'])).
% 0.84/1.06  thf('51', plain,
% 0.84/1.06      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['7', '12'])).
% 0.84/1.06  thf(t36_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.84/1.06  thf('52', plain,
% 0.84/1.06      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.84/1.06      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.84/1.06  thf('53', plain,
% 0.84/1.06      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['7', '12'])).
% 0.84/1.06  thf('54', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.84/1.06          | ((X0) = (k1_xboole_0))
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.84/1.06      inference('demod', [status(thm)], ['10', '11'])).
% 0.84/1.06  thf('55', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r1_tarski @ X0 @ sk_B)
% 0.84/1.06          | ((sk_B) = (k1_xboole_0))
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.84/1.06          | ((X0) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['53', '54'])).
% 0.84/1.06  thf('56', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.84/1.06          | ((k4_xboole_0 @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.84/1.06          | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['52', '55'])).
% 0.84/1.06  thf('57', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.84/1.06          | ((sk_B) = (k1_xboole_0))
% 0.84/1.06          | ((sk_B) = (k1_xboole_0))
% 0.84/1.06          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['51', '56'])).
% 0.84/1.06  thf('58', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.84/1.06          | ((sk_B) = (k1_xboole_0))
% 0.84/1.06          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['57'])).
% 0.84/1.06  thf('59', plain,
% 0.84/1.06      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['42', '49'])).
% 0.84/1.06  thf(t100_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.84/1.06  thf('60', plain,
% 0.84/1.06      (![X12 : $i, X13 : $i]:
% 0.84/1.06         ((k4_xboole_0 @ X12 @ X13)
% 0.84/1.06           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.06  thf('61', plain,
% 0.84/1.06      ((((k4_xboole_0 @ sk_B @ sk_C_2) = (k5_xboole_0 @ sk_B @ sk_C_2))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['59', '60'])).
% 0.84/1.06  thf('62', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf('63', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['45', '48'])).
% 0.84/1.06  thf('64', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['62', '63'])).
% 0.84/1.06  thf('65', plain,
% 0.84/1.06      ((((sk_B) = (k5_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_B @ sk_C_2)))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['61', '64'])).
% 0.84/1.06  thf('66', plain,
% 0.84/1.06      ((((sk_B) = (k5_xboole_0 @ sk_C_2 @ k1_xboole_0))
% 0.84/1.06        | ((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['58', '65'])).
% 0.84/1.06  thf('67', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.84/1.06      inference('cnf', [status(esa)], [t5_boole])).
% 0.84/1.06  thf('68', plain,
% 0.84/1.06      ((((sk_B) = (sk_C_2))
% 0.84/1.06        | ((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['66', '67'])).
% 0.84/1.06  thf('69', plain,
% 0.84/1.06      ((((sk_B) = (k1_xboole_0))
% 0.84/1.06        | ((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B))
% 0.84/1.06        | ((sk_B) = (sk_C_2)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['68'])).
% 0.84/1.06  thf('70', plain,
% 0.84/1.06      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['7', '12'])).
% 0.84/1.06  thf('71', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.84/1.06      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.84/1.06  thf('72', plain, ((((sk_C_2) != (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['70', '71'])).
% 0.84/1.06  thf('73', plain,
% 0.84/1.06      ((((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('clc', [status(thm)], ['69', '72'])).
% 0.84/1.06  thf('74', plain,
% 0.84/1.06      (![X12 : $i, X13 : $i]:
% 0.84/1.06         ((k4_xboole_0 @ X12 @ X13)
% 0.84/1.06           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.06  thf('75', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['45', '48'])).
% 0.84/1.06  thf('76', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k3_xboole_0 @ X1 @ X0)
% 0.84/1.06           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['74', '75'])).
% 0.84/1.06  thf('77', plain,
% 0.84/1.06      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (k5_xboole_0 @ sk_B @ sk_B))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['73', '76'])).
% 0.84/1.06  thf(idempotence_k3_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.84/1.06  thf('78', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.84/1.06  thf('79', plain,
% 0.84/1.06      (![X12 : $i, X13 : $i]:
% 0.84/1.06         ((k4_xboole_0 @ X12 @ X13)
% 0.84/1.06           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.06  thf('80', plain,
% 0.84/1.06      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.84/1.06      inference('sup+', [status(thm)], ['78', '79'])).
% 0.84/1.06  thf('81', plain,
% 0.84/1.06      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.84/1.06      inference('sup+', [status(thm)], ['78', '79'])).
% 0.84/1.06  thf('82', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.84/1.06      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.84/1.06  thf('83', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.06      inference('sup+', [status(thm)], ['81', '82'])).
% 0.84/1.06  thf('84', plain,
% 0.84/1.06      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['77', '80', '83'])).
% 0.84/1.06  thf('85', plain,
% 0.84/1.06      ((((sk_C_2) = (k1_xboole_0))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0))
% 0.84/1.06        | ((sk_B) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['50', '84'])).
% 0.84/1.06  thf('86', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['85'])).
% 0.84/1.06  thf('87', plain,
% 0.84/1.06      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.84/1.06      inference('split', [status(esa)], ['15'])).
% 0.84/1.06  thf('88', plain,
% 0.84/1.06      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('simplify', [status(thm)], ['18'])).
% 0.84/1.06  thf('89', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.06  thf('90', plain,
% 0.84/1.06      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.84/1.06         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('sup+', [status(thm)], ['88', '89'])).
% 0.84/1.06  thf('91', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.84/1.06      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.84/1.06  thf('92', plain,
% 0.84/1.06      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.84/1.06      inference('sup-', [status(thm)], ['90', '91'])).
% 0.84/1.06  thf('93', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['92'])).
% 0.84/1.06  thf('94', plain,
% 0.84/1.06      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.84/1.06      inference('split', [status(esa)], ['15'])).
% 0.84/1.06  thf('95', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.84/1.06      inference('sat_resolution*', [status(thm)], ['93', '94'])).
% 0.84/1.06  thf('96', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.84/1.06      inference('simpl_trail', [status(thm)], ['87', '95'])).
% 0.84/1.06  thf('97', plain, (((sk_B) = (k1_xboole_0))),
% 0.84/1.06      inference('simplify_reflect-', [status(thm)], ['86', '96'])).
% 0.84/1.06  thf('98', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.84/1.06      inference('demod', [status(thm)], ['35', '97'])).
% 0.84/1.06  thf('99', plain, (((sk_C_2) != (sk_C_2))),
% 0.84/1.06      inference('demod', [status(thm)], ['24', '98'])).
% 0.84/1.06  thf('100', plain, ($false), inference('simplify', [status(thm)], ['99'])).
% 0.84/1.06  
% 0.84/1.06  % SZS output end Refutation
% 0.84/1.06  
% 0.84/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
