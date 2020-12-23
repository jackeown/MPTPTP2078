%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n3cqOykMVE

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:26 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 682 expanded)
%              Number of leaves         :   25 ( 208 expanded)
%              Depth                    :   23
%              Number of atoms          :  919 (7002 expanded)
%              Number of equality atoms :  168 (1359 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X57: $i,X58: $i] :
      ( ( X58
        = ( k1_tarski @ X57 ) )
      | ( X58 = k1_xboole_0 )
      | ~ ( r1_tarski @ X58 @ ( k1_tarski @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','44'])).

thf('46',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ( sk_C_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('52',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['50','54','55','57'])).

thf('59',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('61',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('62',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_C_2 @ sk_B )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('70',plain,
    ( ( ( k4_xboole_0 @ sk_C_2 @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,
    ( ( ( k4_xboole_0 @ sk_C_2 @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_C_2 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,
    ( ( sk_C_2
      = ( k3_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('79',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k5_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','84'])).

thf('86',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('87',plain,
    ( ( ( k2_xboole_0 @ sk_C_2 @ sk_B )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('89',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('96',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('97',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['50','54','55','96'])).

thf('98',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['95','97'])).

thf('99',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','58'])).

thf('100',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['94','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['60','100'])).

thf('102',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['59','101'])).

thf('103',plain,(
    $false ),
    inference(simplify,[status(thm)],['102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n3cqOykMVE
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.88  % Solved by: fo/fo7.sh
% 0.70/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.88  % done 1528 iterations in 0.417s
% 0.70/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.88  % SZS output start Refutation
% 0.70/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.88  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.70/0.88  thf(t43_zfmisc_1, conjecture,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.70/0.88          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.70/0.88          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.70/0.88          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.70/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.88        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.70/0.88             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.70/0.88             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.70/0.88             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.70/0.88    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.70/0.88  thf('0', plain,
% 0.70/0.88      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('1', plain,
% 0.70/0.88      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.70/0.88         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('split', [status(esa)], ['0'])).
% 0.70/0.88  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('3', plain,
% 0.70/0.88      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.70/0.88         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.70/0.88  thf(t7_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.88  thf('4', plain,
% 0.70/0.88      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.70/0.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.88  thf('5', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(l3_zfmisc_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.70/0.88       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.70/0.88  thf('6', plain,
% 0.70/0.88      (![X57 : $i, X58 : $i]:
% 0.70/0.88         (((X58) = (k1_tarski @ X57))
% 0.70/0.88          | ((X58) = (k1_xboole_0))
% 0.70/0.88          | ~ (r1_tarski @ X58 @ (k1_tarski @ X57)))),
% 0.70/0.88      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.70/0.88  thf('7', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.70/0.88          | ((X0) = (k1_xboole_0))
% 0.70/0.88          | ((X0) = (k1_tarski @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.70/0.88  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('9', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.70/0.88          | ((X0) = (k1_xboole_0))
% 0.70/0.88          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.70/0.88      inference('demod', [status(thm)], ['7', '8'])).
% 0.70/0.88  thf('10', plain,
% 0.70/0.88      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['4', '9'])).
% 0.70/0.88  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('12', plain,
% 0.70/0.88      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('13', plain,
% 0.70/0.88      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('split', [status(esa)], ['12'])).
% 0.70/0.88  thf('14', plain,
% 0.70/0.88      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.70/0.88         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('sup-', [status(thm)], ['11', '13'])).
% 0.70/0.88  thf('15', plain,
% 0.70/0.88      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.70/0.88         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('sup-', [status(thm)], ['10', '14'])).
% 0.70/0.88  thf('16', plain,
% 0.70/0.88      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('simplify', [status(thm)], ['15'])).
% 0.70/0.88  thf(d3_tarski, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.88  thf('17', plain,
% 0.70/0.88      (![X3 : $i, X5 : $i]:
% 0.70/0.88         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.88  thf('18', plain,
% 0.70/0.88      (![X3 : $i, X5 : $i]:
% 0.70/0.88         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.88  thf('19', plain,
% 0.70/0.88      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['17', '18'])).
% 0.70/0.88  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.70/0.88      inference('simplify', [status(thm)], ['19'])).
% 0.70/0.88  thf(t28_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.70/0.88  thf('21', plain,
% 0.70/0.88      (![X15 : $i, X16 : $i]:
% 0.70/0.88         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.70/0.88      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.88  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.70/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.70/0.88  thf(t100_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.88  thf('23', plain,
% 0.70/0.88      (![X13 : $i, X14 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X13 @ X14)
% 0.70/0.88           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.88  thf('24', plain,
% 0.70/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['22', '23'])).
% 0.70/0.88  thf(t92_xboole_1, axiom,
% 0.70/0.88    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.88  thf('25', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.70/0.88  thf(t91_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.88       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.70/0.88  thf('26', plain,
% 0.70/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.70/0.88           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.70/0.88  thf('27', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.70/0.88           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['25', '26'])).
% 0.70/0.88  thf(t2_boole, axiom,
% 0.70/0.88    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.70/0.88  thf('28', plain,
% 0.70/0.88      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [t2_boole])).
% 0.70/0.88  thf('29', plain,
% 0.70/0.88      (![X13 : $i, X14 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X13 @ X14)
% 0.70/0.88           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.88  thf('30', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['28', '29'])).
% 0.70/0.88  thf(t5_boole, axiom,
% 0.70/0.88    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.88  thf('31', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.70/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.88  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['30', '31'])).
% 0.70/0.88  thf(t98_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.70/0.88  thf('33', plain,
% 0.70/0.88      (![X27 : $i, X28 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X27 @ X28)
% 0.70/0.88           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.88  thf('34', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['32', '33'])).
% 0.70/0.88  thf('35', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.70/0.88           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('demod', [status(thm)], ['27', '34'])).
% 0.70/0.88  thf('36', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.70/0.88           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['24', '35'])).
% 0.70/0.88  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['30', '31'])).
% 0.70/0.88  thf(t48_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.88  thf('38', plain,
% 0.70/0.88      (![X18 : $i, X19 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.70/0.88           = (k3_xboole_0 @ X18 @ X19))),
% 0.70/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.88  thf('39', plain,
% 0.70/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['37', '38'])).
% 0.70/0.88  thf('40', plain,
% 0.70/0.88      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [t2_boole])).
% 0.70/0.88  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.88      inference('demod', [status(thm)], ['39', '40'])).
% 0.70/0.88  thf('42', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.70/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.88  thf('43', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.70/0.88      inference('sup+', [status(thm)], ['41', '42'])).
% 0.70/0.88  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.88      inference('demod', [status(thm)], ['36', '43'])).
% 0.70/0.88  thf('45', plain,
% 0.70/0.88      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.70/0.88         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('sup+', [status(thm)], ['16', '44'])).
% 0.70/0.88  thf('46', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('47', plain,
% 0.70/0.88      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.70/0.88         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('split', [status(esa)], ['0'])).
% 0.70/0.88  thf('48', plain,
% 0.70/0.88      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.70/0.88         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('sup-', [status(thm)], ['46', '47'])).
% 0.70/0.88  thf('49', plain,
% 0.70/0.88      ((((sk_C_2) != (sk_C_2)))
% 0.70/0.88         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.70/0.88             ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('sup-', [status(thm)], ['45', '48'])).
% 0.70/0.88  thf('50', plain,
% 0.70/0.88      ((((sk_B) = (k1_tarski @ sk_A))) | (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.70/0.88      inference('simplify', [status(thm)], ['49'])).
% 0.70/0.88  thf('51', plain,
% 0.70/0.88      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('simplify', [status(thm)], ['15'])).
% 0.70/0.88  thf('52', plain,
% 0.70/0.88      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.70/0.88      inference('split', [status(esa)], ['0'])).
% 0.70/0.88  thf('53', plain,
% 0.70/0.88      ((((sk_B) != (sk_B)))
% 0.70/0.88         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.88      inference('sup-', [status(thm)], ['51', '52'])).
% 0.70/0.88  thf('54', plain,
% 0.70/0.88      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.88      inference('simplify', [status(thm)], ['53'])).
% 0.70/0.88  thf('55', plain,
% 0.70/0.88      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('split', [status(esa)], ['0'])).
% 0.70/0.88  thf('56', plain,
% 0.70/0.88      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('57', plain,
% 0.70/0.88      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.88      inference('split', [status(esa)], ['56'])).
% 0.70/0.88  thf('58', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.70/0.88      inference('sat_resolution*', [status(thm)], ['50', '54', '55', '57'])).
% 0.70/0.88  thf('59', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.70/0.88      inference('simpl_trail', [status(thm)], ['3', '58'])).
% 0.70/0.88  thf('60', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.88      inference('demod', [status(thm)], ['36', '43'])).
% 0.70/0.88  thf('61', plain,
% 0.70/0.88      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['4', '9'])).
% 0.70/0.88  thf('62', plain,
% 0.70/0.88      (![X27 : $i, X28 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X27 @ X28)
% 0.70/0.88           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.88  thf('63', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.70/0.88           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('demod', [status(thm)], ['27', '34'])).
% 0.70/0.88  thf('64', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.88      inference('demod', [status(thm)], ['36', '43'])).
% 0.70/0.88  thf('65', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('demod', [status(thm)], ['63', '64'])).
% 0.70/0.88  thf('66', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X0 @ X1)
% 0.70/0.88           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['62', '65'])).
% 0.70/0.88  thf('67', plain,
% 0.70/0.88      ((((k4_xboole_0 @ sk_C_2 @ sk_B) = (k5_xboole_0 @ sk_B @ sk_B))
% 0.70/0.88        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['61', '66'])).
% 0.70/0.88  thf('68', plain,
% 0.70/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['22', '23'])).
% 0.70/0.88  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.88      inference('demod', [status(thm)], ['39', '40'])).
% 0.70/0.88  thf('70', plain,
% 0.70/0.88      ((((k4_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))
% 0.70/0.88        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.70/0.88  thf('71', plain,
% 0.70/0.88      (![X18 : $i, X19 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.70/0.88           = (k3_xboole_0 @ X18 @ X19))),
% 0.70/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.88  thf('72', plain,
% 0.70/0.88      ((((k4_xboole_0 @ sk_C_2 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_2 @ sk_B))
% 0.70/0.88        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['70', '71'])).
% 0.70/0.88  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['30', '31'])).
% 0.70/0.88  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.88  thf('74', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.88  thf('75', plain,
% 0.70/0.88      ((((sk_C_2) = (k3_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.70/0.88  thf('76', plain,
% 0.70/0.88      (![X13 : $i, X14 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X13 @ X14)
% 0.70/0.88           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.88  thf('77', plain,
% 0.70/0.88      ((((k4_xboole_0 @ sk_B @ sk_C_2) = (k5_xboole_0 @ sk_B @ sk_C_2))
% 0.70/0.88        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['75', '76'])).
% 0.70/0.88  thf('78', plain,
% 0.70/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.70/0.88           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.70/0.88  thf('79', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.70/0.88  thf('80', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.70/0.88           = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['78', '79'])).
% 0.70/0.88  thf('81', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('demod', [status(thm)], ['63', '64'])).
% 0.70/0.88  thf('82', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.70/0.88           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['80', '81'])).
% 0.70/0.88  thf('83', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.70/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.88  thf('84', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.70/0.88      inference('demod', [status(thm)], ['82', '83'])).
% 0.70/0.88  thf('85', plain,
% 0.70/0.88      ((((k5_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_B @ sk_C_2)) = (sk_B))
% 0.70/0.88        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['77', '84'])).
% 0.70/0.88  thf('86', plain,
% 0.70/0.88      (![X27 : $i, X28 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X27 @ X28)
% 0.70/0.88           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.88  thf('87', plain,
% 0.70/0.88      ((((k2_xboole_0 @ sk_C_2 @ sk_B) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('demod', [status(thm)], ['85', '86'])).
% 0.70/0.88  thf('88', plain,
% 0.70/0.88      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.70/0.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.88  thf('89', plain, (((r1_tarski @ sk_C_2 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['87', '88'])).
% 0.70/0.88  thf('90', plain,
% 0.70/0.88      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['4', '9'])).
% 0.70/0.88  thf('91', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.70/0.88          | ((X0) = (k1_xboole_0))
% 0.70/0.88          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.70/0.88      inference('demod', [status(thm)], ['7', '8'])).
% 0.70/0.88  thf('92', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (r1_tarski @ X0 @ sk_B)
% 0.70/0.88          | ((sk_B) = (k1_xboole_0))
% 0.70/0.88          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.70/0.88          | ((X0) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['90', '91'])).
% 0.70/0.88  thf('93', plain,
% 0.70/0.88      ((((sk_B) = (k1_xboole_0))
% 0.70/0.88        | ((sk_C_2) = (k1_xboole_0))
% 0.70/0.88        | ((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.70/0.88        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['89', '92'])).
% 0.70/0.88  thf('94', plain,
% 0.70/0.88      ((((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.70/0.88        | ((sk_C_2) = (k1_xboole_0))
% 0.70/0.88        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.88      inference('simplify', [status(thm)], ['93'])).
% 0.70/0.88  thf('95', plain,
% 0.70/0.88      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.70/0.88      inference('split', [status(esa)], ['12'])).
% 0.70/0.88  thf('96', plain,
% 0.70/0.88      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.88      inference('split', [status(esa)], ['12'])).
% 0.70/0.88  thf('97', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.70/0.88      inference('sat_resolution*', [status(thm)], ['50', '54', '55', '96'])).
% 0.70/0.88  thf('98', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.70/0.88      inference('simpl_trail', [status(thm)], ['95', '97'])).
% 0.70/0.88  thf('99', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.70/0.88      inference('simpl_trail', [status(thm)], ['3', '58'])).
% 0.70/0.88  thf('100', plain, (((sk_B) = (k1_xboole_0))),
% 0.70/0.88      inference('simplify_reflect-', [status(thm)], ['94', '98', '99'])).
% 0.70/0.88  thf('101', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.70/0.88      inference('demod', [status(thm)], ['60', '100'])).
% 0.70/0.88  thf('102', plain, (((sk_C_2) != (sk_C_2))),
% 0.70/0.88      inference('demod', [status(thm)], ['59', '101'])).
% 0.70/0.88  thf('103', plain, ($false), inference('simplify', [status(thm)], ['102'])).
% 0.70/0.88  
% 0.70/0.88  % SZS output end Refutation
% 0.70/0.88  
% 0.74/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
