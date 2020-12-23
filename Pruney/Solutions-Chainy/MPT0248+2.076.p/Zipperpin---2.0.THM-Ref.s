%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TGjfIMAPoe

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:29 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 396 expanded)
%              Number of leaves         :   25 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          :  826 (4908 expanded)
%              Number of equality atoms :  147 (1043 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
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

thf('25',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','37'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('40',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('47',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('49',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('52',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('55',plain,(
    ! [X18: $i] :
      ( ( r1_xboole_0 @ X18 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('56',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','71'])).

thf('73',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ X0 @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('78',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','79'])).

thf('81',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('82',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('85',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(simpl_trail,[status(thm)],['72','85'])).

thf('87',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['24','86'])).

thf('88',plain,(
    $false ),
    inference(simplify,[status(thm)],['87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TGjfIMAPoe
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 295 iterations in 0.122s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.58  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(t43_zfmisc_1, conjecture,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.41/0.58          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.41/0.58          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.41/0.58          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.58        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.41/0.58             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.41/0.58             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.41/0.58             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.41/0.58         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.41/0.58         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.41/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.41/0.58      inference('split', [status(esa)], ['5'])).
% 0.41/0.58  thf(t7_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.41/0.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.58  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(l3_zfmisc_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.41/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      (![X56 : $i, X57 : $i]:
% 0.41/0.58         (((X57) = (k1_tarski @ X56))
% 0.41/0.58          | ((X57) = (k1_xboole_0))
% 0.41/0.58          | ~ (r1_tarski @ X57 @ (k1_tarski @ X56)))),
% 0.41/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.41/0.58          | ((X0) = (k1_xboole_0))
% 0.41/0.58          | ((X0) = (k1_tarski @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.58  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.41/0.58          | ((X0) = (k1_xboole_0))
% 0.41/0.58          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['7', '12'])).
% 0.41/0.59  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('split', [status(esa)], ['15'])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.41/0.59         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['14', '16'])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.41/0.59         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['13', '17'])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      ((((sk_B) != (sk_B)))
% 0.41/0.59         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.41/0.59  thf('23', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 0.41/0.59  thf('24', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['7', '12'])).
% 0.41/0.59  thf(t95_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k3_xboole_0 @ A @ B ) =
% 0.41/0.59       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (![X26 : $i, X27 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ X26 @ X27)
% 0.41/0.59           = (k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ 
% 0.41/0.59              (k2_xboole_0 @ X26 @ X27)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.41/0.59  thf(t91_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.59       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.41/0.59           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (![X26 : $i, X27 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ X26 @ X27)
% 0.41/0.59           = (k5_xboole_0 @ X26 @ 
% 0.41/0.59              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 0.41/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 0.41/0.59          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ sk_B)))
% 0.41/0.59        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['25', '28'])).
% 0.41/0.59  thf(commutativity_k5_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.41/0.59  thf(t92_xboole_1, axiom,
% 0.41/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.59  thf('31', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.41/0.59           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.59           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['31', '32'])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.41/0.59  thf(t5_boole, axiom,
% 0.41/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.59  thf('35', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.59  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['33', '36'])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['29', '30', '37'])).
% 0.41/0.59  thf(t17_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.41/0.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.41/0.59  thf('40', plain, (((r1_tarski @ sk_C_2 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['38', '39'])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['7', '12'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.41/0.59          | ((X0) = (k1_xboole_0))
% 0.41/0.59          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.41/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X0 @ sk_B)
% 0.41/0.59          | ((sk_B) = (k1_xboole_0))
% 0.41/0.59          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.41/0.59          | ((X0) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      ((((sk_B) = (k1_xboole_0))
% 0.41/0.59        | ((sk_C_2) = (k1_xboole_0))
% 0.41/0.59        | ((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.41/0.59        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['40', '43'])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      ((((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.41/0.59        | ((sk_C_2) = (k1_xboole_0))
% 0.41/0.59        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['44'])).
% 0.41/0.59  thf('46', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.41/0.59  thf('47', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.41/0.59      inference('split', [status(esa)], ['15'])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      (((((sk_C_2) != (sk_C_2)) | ((sk_B) = (k1_xboole_0))))
% 0.41/0.59         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['49'])).
% 0.41/0.59  thf('51', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      (![X26 : $i, X27 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ X26 @ X27)
% 0.41/0.59           = (k5_xboole_0 @ X26 @ 
% 0.41/0.59              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 0.41/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.59           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['51', '52'])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 0.41/0.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.41/0.59  thf(t66_xboole_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.41/0.59       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (![X18 : $i]: ((r1_xboole_0 @ X18 @ X18) | ((X18) != (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.41/0.59  thf('56', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('simplify', [status(thm)], ['55'])).
% 0.41/0.59  thf(d3_tarski, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.59  thf('57', plain,
% 0.41/0.59      (![X3 : $i, X5 : $i]:
% 0.41/0.59         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      (![X3 : $i, X5 : $i]:
% 0.41/0.59         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.59  thf(t3_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.41/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.41/0.59  thf('59', plain,
% 0.41/0.59      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X10 @ X8)
% 0.41/0.59          | ~ (r2_hidden @ X10 @ X11)
% 0.41/0.59          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.59  thf('60', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((r1_tarski @ X0 @ X1)
% 0.41/0.59          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.41/0.59          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.41/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r1_tarski @ X0 @ X1)
% 0.41/0.59          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.41/0.59          | (r1_tarski @ X0 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['57', '60'])).
% 0.41/0.59  thf('62', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.41/0.59      inference('simplify', [status(thm)], ['61'])).
% 0.41/0.59  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.41/0.59      inference('sup-', [status(thm)], ['56', '62'])).
% 0.41/0.59  thf(d10_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('64', plain,
% 0.41/0.59      (![X12 : $i, X14 : $i]:
% 0.41/0.59         (((X12) = (X14))
% 0.41/0.59          | ~ (r1_tarski @ X14 @ X12)
% 0.41/0.59          | ~ (r1_tarski @ X12 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('65', plain,
% 0.41/0.59      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.41/0.59  thf('66', plain,
% 0.41/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['54', '65'])).
% 0.41/0.59  thf('67', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['53', '66'])).
% 0.41/0.59  thf('68', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['33', '36'])).
% 0.41/0.59  thf('69', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['67', '68'])).
% 0.41/0.59  thf('70', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.59  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['69', '70'])).
% 0.41/0.59  thf('72', plain,
% 0.41/0.59      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.41/0.59         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['50', '71'])).
% 0.41/0.59  thf('73', plain,
% 0.41/0.59      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.59  thf('74', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['67', '68'])).
% 0.41/0.59  thf('75', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ sk_B)))
% 0.41/0.59         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['73', '74'])).
% 0.41/0.59  thf('76', plain,
% 0.41/0.59      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.59  thf('77', plain,
% 0.41/0.59      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.59  thf('78', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.59  thf('79', plain,
% 0.41/0.59      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B) = (X0)))
% 0.41/0.59         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['77', '78'])).
% 0.41/0.59  thf('80', plain,
% 0.41/0.59      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.41/0.59         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('demod', [status(thm)], ['75', '76', '79'])).
% 0.41/0.59  thf('81', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.41/0.59  thf('82', plain,
% 0.41/0.59      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.59  thf('83', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['82'])).
% 0.41/0.59  thf('84', plain,
% 0.41/0.59      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('split', [status(esa)], ['15'])).
% 0.41/0.59  thf('85', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.41/0.59  thf('86', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['72', '85'])).
% 0.41/0.59  thf('87', plain, (((sk_C_2) != (sk_C_2))),
% 0.41/0.59      inference('demod', [status(thm)], ['24', '86'])).
% 0.41/0.59  thf('88', plain, ($false), inference('simplify', [status(thm)], ['87'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
