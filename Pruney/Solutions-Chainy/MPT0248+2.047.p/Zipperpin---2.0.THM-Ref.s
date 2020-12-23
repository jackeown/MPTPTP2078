%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8ytL03IFKQ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:24 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 609 expanded)
%              Number of leaves         :   29 ( 185 expanded)
%              Depth                    :   25
%              Number of atoms          : 1128 (6091 expanded)
%              Number of equality atoms :  178 (1128 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
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
    ! [X56: $i,X57: $i] :
      ( ( X57
        = ( k1_tarski @ X56 ) )
      | ( X57 = k1_xboole_0 )
      | ~ ( r1_tarski @ X57 @ ( k1_tarski @ X56 ) ) ) ),
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X57: $i,X58: $i] :
      ( ( r1_tarski @ X57 @ ( k1_tarski @ X58 ) )
      | ( X57 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('27',plain,(
    ! [X58: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X58 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('45',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','50'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('55',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
      | ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['55','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('72',plain,
    ( ( sk_C_2 != sk_C_2 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_xboole_0 @ sk_C_2 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('80',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
      = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','50'])).

thf('83',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('89',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','89'])).

thf('91',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['90'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('92',plain,(
    ! [X34: $i] :
      ( ( k5_xboole_0 @ X34 @ X34 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('93',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_C_2
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('99',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('107',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X34: $i] :
      ( ( k5_xboole_0 @ X34 @ X34 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('111',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('114',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','105','113'])).

thf('115',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('116',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('117',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','50'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('122',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('125',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['123','124'])).

thf('126',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['115','125'])).

thf('127',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['114','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['53','127'])).

thf('129',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['24','128'])).

thf('130',plain,(
    $false ),
    inference(simplify,[status(thm)],['129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8ytL03IFKQ
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 523 iterations in 0.138s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.37/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.60  thf(t43_zfmisc_1, conjecture,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.60          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.37/0.60          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.37/0.60          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.60        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.60             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.37/0.60             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.37/0.60             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.37/0.60         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.37/0.60         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.60      inference('split', [status(esa)], ['5'])).
% 0.37/0.60  thf(t7_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.37/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.60  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(l3_zfmisc_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.37/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (![X56 : $i, X57 : $i]:
% 0.37/0.60         (((X57) = (k1_tarski @ X56))
% 0.37/0.60          | ((X57) = (k1_xboole_0))
% 0.37/0.60          | ~ (r1_tarski @ X57 @ (k1_tarski @ X56)))),
% 0.37/0.60      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.37/0.60          | ((X0) = (k1_xboole_0))
% 0.37/0.60          | ((X0) = (k1_tarski @ sk_A)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.60  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.37/0.60          | ((X0) = (k1_xboole_0))
% 0.37/0.60          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.37/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['7', '12'])).
% 0.37/0.60  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('split', [status(esa)], ['15'])).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.37/0.60         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['14', '16'])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.37/0.60         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['13', '17'])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      ((((sk_B) != (sk_B)))
% 0.37/0.60         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.60  thf('23', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.37/0.60      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 0.37/0.60  thf('24', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.37/0.60      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.37/0.60  thf(d3_tarski, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      (![X5 : $i, X7 : $i]:
% 0.37/0.60         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.37/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      (![X57 : $i, X58 : $i]:
% 0.37/0.60         ((r1_tarski @ X57 @ (k1_tarski @ X58)) | ((X57) != (k1_xboole_0)))),
% 0.37/0.60      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (![X58 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X58))),
% 0.37/0.60      inference('simplify', [status(thm)], ['26'])).
% 0.37/0.60  thf(t28_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.60  thf('28', plain,
% 0.37/0.60      (![X26 : $i, X27 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 0.37/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.60  thf(t100_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (![X17 : $i, X18 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X17 @ X18)
% 0.37/0.60           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf(commutativity_k5_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.60  thf(t5_boole, axiom,
% 0.37/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.60  thf('32', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 0.37/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.60  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['30', '33'])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['29', '34'])).
% 0.37/0.60  thf('36', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['30', '33'])).
% 0.37/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.60  thf('37', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.60  thf(t4_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.37/0.60          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.37/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.60  thf('39', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.60          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.60  thf('40', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.37/0.60          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['36', '39'])).
% 0.37/0.60  thf('41', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.37/0.60          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['35', '40'])).
% 0.37/0.60  thf('42', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['29', '34'])).
% 0.37/0.60  thf('43', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['30', '33'])).
% 0.37/0.60  thf('44', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.60  thf(d7_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.60  thf('45', plain,
% 0.37/0.60      (![X8 : $i, X10 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X8 @ X10)
% 0.37/0.60          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.60  thf('46', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.60  thf('47', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.37/0.60          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['43', '46'])).
% 0.37/0.60  thf('48', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.60          | (r1_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['42', '47'])).
% 0.37/0.60  thf('49', plain,
% 0.37/0.60      (![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)),
% 0.37/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.37/0.60  thf('50', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.60      inference('demod', [status(thm)], ['41', '49'])).
% 0.37/0.60  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.60      inference('sup-', [status(thm)], ['25', '50'])).
% 0.37/0.60  thf(t12_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.37/0.60  thf('52', plain,
% 0.37/0.60      (![X19 : $i, X20 : $i]:
% 0.37/0.60         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 0.37/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.60  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.60  thf('54', plain,
% 0.37/0.60      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['7', '12'])).
% 0.37/0.60  thf('55', plain,
% 0.37/0.60      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['7', '12'])).
% 0.37/0.60  thf(t17_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.60  thf('56', plain,
% 0.37/0.60      (![X24 : $i, X25 : $i]: (r1_tarski @ (k3_xboole_0 @ X24 @ X25) @ X24)),
% 0.37/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.60  thf('57', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.37/0.60          | ((X0) = (k1_xboole_0))
% 0.37/0.60          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.37/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.60  thf('58', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0)
% 0.37/0.60            = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.37/0.60          | ((k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.60  thf('59', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.60  thf('60', plain,
% 0.37/0.60      (![X24 : $i, X25 : $i]: (r1_tarski @ (k3_xboole_0 @ X24 @ X25) @ X24)),
% 0.37/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.60  thf('61', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.37/0.60      inference('sup+', [status(thm)], ['59', '60'])).
% 0.37/0.60  thf('62', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0)
% 0.37/0.60          | ((k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['58', '61'])).
% 0.37/0.60  thf('63', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.60  thf('64', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.60          | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0)
% 0.37/0.60          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.60  thf('65', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.37/0.60          | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0))),
% 0.37/0.60      inference('simplify', [status(thm)], ['64'])).
% 0.37/0.60  thf('66', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r1_tarski @ sk_B @ X0)
% 0.37/0.60          | ((sk_B) = (k1_xboole_0))
% 0.37/0.60          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['55', '65'])).
% 0.37/0.60  thf('67', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X0 @ sk_B)
% 0.37/0.60          | ((sk_B) = (k1_xboole_0))
% 0.37/0.60          | ((sk_B) = (k1_xboole_0))
% 0.37/0.60          | (r1_tarski @ sk_B @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['54', '66'])).
% 0.37/0.60  thf('68', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r1_tarski @ sk_B @ X0)
% 0.37/0.60          | ((sk_B) = (k1_xboole_0))
% 0.37/0.60          | (r1_xboole_0 @ X0 @ sk_B))),
% 0.37/0.60      inference('simplify', [status(thm)], ['67'])).
% 0.37/0.60  thf('69', plain,
% 0.37/0.60      (![X19 : $i, X20 : $i]:
% 0.37/0.60         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 0.37/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.60  thf('70', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X0 @ sk_B)
% 0.37/0.60          | ((sk_B) = (k1_xboole_0))
% 0.37/0.60          | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.60  thf('71', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.37/0.60      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.37/0.60  thf('72', plain,
% 0.37/0.60      ((((sk_C_2) != (sk_C_2))
% 0.37/0.60        | ((sk_B) = (k1_xboole_0))
% 0.37/0.60        | (r1_xboole_0 @ sk_C_2 @ sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.37/0.60  thf('73', plain,
% 0.37/0.60      (((r1_xboole_0 @ sk_C_2 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['72'])).
% 0.37/0.60  thf('74', plain,
% 0.37/0.60      (![X8 : $i, X9 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.37/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.60  thf('75', plain,
% 0.37/0.60      ((((sk_B) = (k1_xboole_0))
% 0.37/0.60        | ((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['73', '74'])).
% 0.37/0.60  thf('76', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.60  thf('77', plain,
% 0.37/0.60      ((((sk_B) = (k1_xboole_0))
% 0.37/0.60        | ((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0)))),
% 0.37/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.60  thf('78', plain,
% 0.37/0.60      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['7', '12'])).
% 0.37/0.60  thf(l98_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k5_xboole_0 @ A @ B ) =
% 0.37/0.60       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.60  thf('79', plain,
% 0.37/0.60      (![X15 : $i, X16 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ X15 @ X16)
% 0.37/0.60           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 0.37/0.60              (k3_xboole_0 @ X15 @ X16)))),
% 0.37/0.60      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.37/0.60  thf('80', plain,
% 0.37/0.60      ((((k5_xboole_0 @ sk_B @ sk_C_2)
% 0.37/0.60          = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C_2)))
% 0.37/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['78', '79'])).
% 0.37/0.60  thf('81', plain,
% 0.37/0.60      ((((k5_xboole_0 @ sk_B @ sk_C_2) = (k4_xboole_0 @ sk_B @ k1_xboole_0))
% 0.37/0.60        | ((sk_B) = (k1_xboole_0))
% 0.37/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['77', '80'])).
% 0.37/0.60  thf('82', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.60      inference('sup-', [status(thm)], ['25', '50'])).
% 0.37/0.60  thf('83', plain,
% 0.37/0.60      (![X26 : $i, X27 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 0.37/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.60  thf('84', plain,
% 0.37/0.60      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['82', '83'])).
% 0.37/0.60  thf('85', plain,
% 0.37/0.60      (![X15 : $i, X16 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ X15 @ X16)
% 0.37/0.60           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 0.37/0.60              (k3_xboole_0 @ X15 @ X16)))),
% 0.37/0.60      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.37/0.60  thf('86', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.60           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['84', '85'])).
% 0.37/0.60  thf('87', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.60  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.60  thf('89', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.37/0.60  thf('90', plain,
% 0.37/0.60      ((((k5_xboole_0 @ sk_B @ sk_C_2) = (sk_B))
% 0.37/0.60        | ((sk_B) = (k1_xboole_0))
% 0.37/0.60        | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('demod', [status(thm)], ['81', '89'])).
% 0.37/0.60  thf('91', plain,
% 0.37/0.60      ((((sk_B) = (k1_xboole_0)) | ((k5_xboole_0 @ sk_B @ sk_C_2) = (sk_B)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['90'])).
% 0.37/0.60  thf(t92_xboole_1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.60  thf('92', plain, (![X34 : $i]: ((k5_xboole_0 @ X34 @ X34) = (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.60  thf(t91_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.60       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.60  thf('93', plain,
% 0.37/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ X33)
% 0.37/0.60           = (k5_xboole_0 @ X31 @ (k5_xboole_0 @ X32 @ X33)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.60  thf('94', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.60           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['92', '93'])).
% 0.37/0.60  thf('95', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.60  thf('96', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('demod', [status(thm)], ['94', '95'])).
% 0.37/0.60  thf('97', plain,
% 0.37/0.60      ((((sk_C_2) = (k5_xboole_0 @ sk_B @ sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['91', '96'])).
% 0.37/0.60  thf('98', plain,
% 0.37/0.60      (![X5 : $i, X7 : $i]:
% 0.37/0.60         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.37/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.60  thf('99', plain,
% 0.37/0.60      (![X5 : $i, X7 : $i]:
% 0.37/0.60         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 0.37/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.60  thf('100', plain,
% 0.37/0.60      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['98', '99'])).
% 0.37/0.60  thf('101', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.60      inference('simplify', [status(thm)], ['100'])).
% 0.37/0.60  thf('102', plain,
% 0.37/0.60      (![X26 : $i, X27 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 0.37/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.60  thf('103', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['101', '102'])).
% 0.37/0.60  thf('104', plain,
% 0.37/0.60      (![X17 : $i, X18 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X17 @ X18)
% 0.37/0.60           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf('105', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['103', '104'])).
% 0.37/0.60  thf('106', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['101', '102'])).
% 0.37/0.60  thf('107', plain,
% 0.37/0.60      (![X15 : $i, X16 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ X15 @ X16)
% 0.37/0.60           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 0.37/0.60              (k3_xboole_0 @ X15 @ X16)))),
% 0.37/0.60      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.37/0.60  thf('108', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ X0 @ X0)
% 0.37/0.60           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['106', '107'])).
% 0.37/0.60  thf('109', plain, (![X34 : $i]: ((k5_xboole_0 @ X34 @ X34) = (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.60  thf('110', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.60      inference('simplify', [status(thm)], ['100'])).
% 0.37/0.60  thf('111', plain,
% 0.37/0.60      (![X19 : $i, X20 : $i]:
% 0.37/0.60         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 0.37/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.60  thf('112', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['110', '111'])).
% 0.37/0.60  thf('113', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['108', '109', '112'])).
% 0.37/0.60  thf('114', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.37/0.60      inference('demod', [status(thm)], ['97', '105', '113'])).
% 0.37/0.60  thf('115', plain,
% 0.37/0.60      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.37/0.60      inference('split', [status(esa)], ['15'])).
% 0.37/0.60  thf('116', plain,
% 0.37/0.60      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.60  thf('117', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.60      inference('sup-', [status(thm)], ['25', '50'])).
% 0.37/0.60  thf('118', plain,
% 0.37/0.60      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 0.37/0.60         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('sup+', [status(thm)], ['116', '117'])).
% 0.37/0.60  thf('119', plain,
% 0.37/0.60      (![X19 : $i, X20 : $i]:
% 0.37/0.60         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 0.37/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.60  thf('120', plain,
% 0.37/0.60      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.37/0.60         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['118', '119'])).
% 0.37/0.60  thf('121', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.37/0.60      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.37/0.60  thf('122', plain,
% 0.37/0.60      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['120', '121'])).
% 0.37/0.60  thf('123', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['122'])).
% 0.37/0.60  thf('124', plain,
% 0.37/0.60      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.60      inference('split', [status(esa)], ['15'])).
% 0.37/0.60  thf('125', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.60      inference('sat_resolution*', [status(thm)], ['123', '124'])).
% 0.37/0.60  thf('126', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.37/0.60      inference('simpl_trail', [status(thm)], ['115', '125'])).
% 0.37/0.60  thf('127', plain, (((sk_B) = (k1_xboole_0))),
% 0.37/0.60      inference('simplify_reflect-', [status(thm)], ['114', '126'])).
% 0.37/0.60  thf('128', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['53', '127'])).
% 0.37/0.60  thf('129', plain, (((sk_C_2) != (sk_C_2))),
% 0.37/0.60      inference('demod', [status(thm)], ['24', '128'])).
% 0.37/0.60  thf('130', plain, ($false), inference('simplify', [status(thm)], ['129'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
