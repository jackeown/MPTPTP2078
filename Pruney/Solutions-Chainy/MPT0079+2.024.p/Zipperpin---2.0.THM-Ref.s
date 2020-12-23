%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DKWaIlk7NL

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:00 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 687 expanded)
%              Number of leaves         :   28 ( 235 expanded)
%              Depth                    :   15
%              Number of atoms          :  820 (5343 expanded)
%              Number of equality atoms :   90 ( 587 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['0','5'])).

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

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_D ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X32 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X29 @ X30 ) @ ( k4_xboole_0 @ X29 @ X30 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['12','13'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['14','17'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_D ) @ sk_B )
    = sk_D ),
    inference('sup+',[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_D ),
    inference('sup-',[status(thm)],['48','53'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) )
    = sk_D ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X32 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X29 @ X30 ) @ ( k4_xboole_0 @ X29 @ X30 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('65',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('69',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_C_2 )
    = sk_A ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = sk_A ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['58','71','72'])).

thf('74',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('76',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('78',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('80',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('82',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['36','39'])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['73','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['45','85'])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('88',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('89',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['73','84'])).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('92',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['73','84'])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['65','66'])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,(
    sk_B = sk_C_2 ),
    inference('sup+',[status(thm)],['86','94'])).

thf('96',plain,(
    sk_C_2 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DKWaIlk7NL
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:48:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.55/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.75  % Solved by: fo/fo7.sh
% 0.55/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.75  % done 956 iterations in 0.286s
% 0.55/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.75  % SZS output start Refutation
% 0.55/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.75  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.55/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.75  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.55/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.75  thf(t72_xboole_1, conjecture,
% 0.55/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.55/0.75         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.55/0.75       ( ( C ) = ( B ) ) ))).
% 0.55/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.55/0.75            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.55/0.75          ( ( C ) = ( B ) ) ) )),
% 0.55/0.75    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.55/0.75  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(t4_xboole_0, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.75            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.55/0.75  thf('1', plain,
% 0.55/0.75      (![X8 : $i, X9 : $i]:
% 0.55/0.75         ((r1_xboole_0 @ X8 @ X9)
% 0.55/0.75          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.75  thf(commutativity_k3_xboole_0, axiom,
% 0.55/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.55/0.75  thf('2', plain,
% 0.55/0.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('3', plain,
% 0.55/0.75      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.55/0.75         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.55/0.75          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.55/0.75      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.75  thf('4', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.75         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.75          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.75  thf('5', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['1', '4'])).
% 0.55/0.75  thf('6', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.55/0.75      inference('sup-', [status(thm)], ['0', '5'])).
% 0.55/0.75  thf(t3_xboole_0, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.55/0.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.75            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.55/0.75  thf('7', plain,
% 0.55/0.75      (![X4 : $i, X5 : $i]:
% 0.55/0.75         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.55/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.75  thf('8', plain,
% 0.55/0.75      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.55/0.75         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.55/0.75          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.55/0.75      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.75  thf('9', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.75         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.55/0.75          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['7', '8'])).
% 0.55/0.75  thf('10', plain,
% 0.55/0.75      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_D) @ X0)),
% 0.55/0.75      inference('sup-', [status(thm)], ['6', '9'])).
% 0.55/0.75  thf(t66_xboole_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.55/0.75       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.55/0.75  thf('11', plain,
% 0.55/0.75      (![X32 : $i]: (((X32) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X32 @ X32))),
% 0.55/0.75      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.55/0.75  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['10', '11'])).
% 0.55/0.75  thf(t51_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.55/0.75       ( A ) ))).
% 0.55/0.75  thf('13', plain,
% 0.55/0.75      (![X29 : $i, X30 : $i]:
% 0.55/0.75         ((k2_xboole_0 @ (k3_xboole_0 @ X29 @ X30) @ (k4_xboole_0 @ X29 @ X30))
% 0.55/0.75           = (X29))),
% 0.55/0.75      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.55/0.75  thf('14', plain,
% 0.55/0.75      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['12', '13'])).
% 0.55/0.75  thf(commutativity_k2_xboole_0, axiom,
% 0.55/0.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.55/0.75  thf('15', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.75  thf(t1_boole, axiom,
% 0.55/0.75    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.75  thf('16', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.55/0.75      inference('cnf', [status(esa)], [t1_boole])).
% 0.55/0.75  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['15', '16'])).
% 0.55/0.75  thf('18', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['14', '17'])).
% 0.55/0.75  thf(t40_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.55/0.75  thf('19', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.55/0.75           = (k4_xboole_0 @ X17 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.55/0.75  thf(t48_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.75  thf('20', plain,
% 0.55/0.75      (![X24 : $i, X25 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.55/0.75           = (k3_xboole_0 @ X24 @ X25))),
% 0.55/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.75  thf('21', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.55/0.75           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['19', '20'])).
% 0.55/0.75  thf('22', plain,
% 0.55/0.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('23', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.55/0.75           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.55/0.75  thf('24', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.75  thf(t46_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.55/0.75  thf('25', plain,
% 0.55/0.75      (![X22 : $i, X23 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ X22 @ (k2_xboole_0 @ X22 @ X23)) = (k1_xboole_0))),
% 0.55/0.75      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.55/0.75  thf('26', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['24', '25'])).
% 0.55/0.75  thf('27', plain,
% 0.55/0.75      (![X24 : $i, X25 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.55/0.75           = (k3_xboole_0 @ X24 @ X25))),
% 0.55/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.75  thf('28', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.55/0.75           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['26', '27'])).
% 0.55/0.75  thf(t39_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.75  thf('29', plain,
% 0.55/0.75      (![X15 : $i, X16 : $i]:
% 0.55/0.75         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.55/0.75           = (k2_xboole_0 @ X15 @ X16))),
% 0.55/0.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.55/0.75  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['15', '16'])).
% 0.55/0.75  thf('31', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['29', '30'])).
% 0.55/0.75  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['15', '16'])).
% 0.55/0.75  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['31', '32'])).
% 0.55/0.75  thf('34', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.75      inference('demod', [status(thm)], ['28', '33'])).
% 0.55/0.75  thf('35', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.55/0.75           = (X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['23', '34'])).
% 0.55/0.75  thf('36', plain,
% 0.55/0.75      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_D) @ sk_B) = (sk_D))),
% 0.55/0.75      inference('sup+', [status(thm)], ['18', '35'])).
% 0.55/0.75  thf('37', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.75  thf('38', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.55/0.75           = (k4_xboole_0 @ X17 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.55/0.75  thf('39', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.55/0.75           = (k4_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['37', '38'])).
% 0.55/0.75  thf('40', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.55/0.75      inference('demod', [status(thm)], ['36', '39'])).
% 0.55/0.75  thf('41', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.55/0.75           = (X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['23', '34'])).
% 0.55/0.75  thf('42', plain,
% 0.55/0.75      (((k4_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_D) = (sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['40', '41'])).
% 0.55/0.75  thf('43', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.75  thf('44', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.55/0.75           = (k4_xboole_0 @ X17 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.55/0.75  thf('45', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.55/0.75  thf('46', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.75  thf(t7_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.75  thf('47', plain,
% 0.55/0.75      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 0.55/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.75  thf('48', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['46', '47'])).
% 0.55/0.75  thf('49', plain,
% 0.55/0.75      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C_2 @ sk_D))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('50', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.75  thf('51', plain,
% 0.55/0.75      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_2 @ sk_D))),
% 0.55/0.75      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.75  thf(t43_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.55/0.75       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.55/0.75  thf('52', plain,
% 0.55/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.55/0.75         ((r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.55/0.75          | ~ (r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.55/0.75  thf('53', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.55/0.75          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_2) @ sk_D))),
% 0.55/0.75      inference('sup-', [status(thm)], ['51', '52'])).
% 0.55/0.75  thf('54', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_D)),
% 0.55/0.75      inference('sup-', [status(thm)], ['48', '53'])).
% 0.55/0.75  thf(t12_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.55/0.75  thf('55', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i]:
% 0.55/0.75         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.55/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.55/0.75  thf('56', plain,
% 0.55/0.75      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_D) = (sk_D))),
% 0.55/0.75      inference('sup-', [status(thm)], ['54', '55'])).
% 0.55/0.75  thf('57', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.75  thf('58', plain,
% 0.55/0.75      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_C_2)) = (sk_D))),
% 0.55/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.55/0.75  thf('59', plain, ((r1_xboole_0 @ sk_C_2 @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('60', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.75         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.55/0.75          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['7', '8'])).
% 0.55/0.75  thf('61', plain,
% 0.55/0.75      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ X0)),
% 0.55/0.75      inference('sup-', [status(thm)], ['59', '60'])).
% 0.55/0.75  thf('62', plain,
% 0.55/0.75      (![X32 : $i]: (((X32) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X32 @ X32))),
% 0.55/0.75      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.55/0.75  thf('63', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['61', '62'])).
% 0.55/0.75  thf('64', plain,
% 0.55/0.75      (![X29 : $i, X30 : $i]:
% 0.55/0.75         ((k2_xboole_0 @ (k3_xboole_0 @ X29 @ X30) @ (k4_xboole_0 @ X29 @ X30))
% 0.55/0.75           = (X29))),
% 0.55/0.75      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.55/0.75  thf('65', plain,
% 0.55/0.75      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ sk_A)) = (sk_C_2))),
% 0.55/0.75      inference('sup+', [status(thm)], ['63', '64'])).
% 0.55/0.75  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['15', '16'])).
% 0.55/0.75  thf('67', plain, (((k4_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 0.55/0.75      inference('demod', [status(thm)], ['65', '66'])).
% 0.55/0.75  thf('68', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.55/0.75           = (X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['23', '34'])).
% 0.55/0.75  thf('69', plain,
% 0.55/0.75      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_C_2) = (sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['67', '68'])).
% 0.55/0.75  thf('70', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.55/0.75           = (k4_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['37', '38'])).
% 0.55/0.75  thf('71', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['69', '70'])).
% 0.55/0.75  thf('72', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.75  thf('73', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_D))),
% 0.55/0.75      inference('demod', [status(thm)], ['58', '71', '72'])).
% 0.55/0.75  thf('74', plain,
% 0.55/0.75      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_2 @ sk_D))),
% 0.55/0.75      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.75  thf('75', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.55/0.75      inference('sup+', [status(thm)], ['46', '47'])).
% 0.55/0.75  thf('76', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['74', '75'])).
% 0.55/0.75  thf('77', plain,
% 0.55/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.55/0.75         ((r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.55/0.75          | ~ (r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.55/0.75  thf('78', plain, ((r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('79', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i]:
% 0.55/0.75         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.55/0.75      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.55/0.75  thf('80', plain,
% 0.55/0.75      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A) = (sk_A))),
% 0.55/0.75      inference('sup-', [status(thm)], ['78', '79'])).
% 0.55/0.75  thf('81', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.75  thf('82', plain,
% 0.55/0.75      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['80', '81'])).
% 0.55/0.75  thf('83', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.55/0.75      inference('demod', [status(thm)], ['36', '39'])).
% 0.55/0.75  thf('84', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['82', '83'])).
% 0.55/0.75  thf('85', plain, (((sk_D) = (sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['73', '84'])).
% 0.55/0.75  thf('86', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['45', '85'])).
% 0.55/0.75  thf('87', plain,
% 0.55/0.75      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_2 @ sk_D))),
% 0.55/0.75      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.75  thf('88', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.55/0.75           = (k4_xboole_0 @ X17 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.55/0.75  thf('89', plain,
% 0.55/0.75      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.55/0.75         = (k4_xboole_0 @ sk_C_2 @ sk_D))),
% 0.55/0.75      inference('sup+', [status(thm)], ['87', '88'])).
% 0.55/0.75  thf('90', plain, (((sk_D) = (sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['73', '84'])).
% 0.55/0.75  thf('91', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i]:
% 0.55/0.75         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 0.55/0.75           = (k4_xboole_0 @ X17 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.55/0.75  thf('92', plain, (((sk_D) = (sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['73', '84'])).
% 0.55/0.75  thf('93', plain, (((k4_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 0.55/0.75      inference('demod', [status(thm)], ['65', '66'])).
% 0.55/0.75  thf('94', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C_2))),
% 0.55/0.75      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 0.55/0.75  thf('95', plain, (((sk_B) = (sk_C_2))),
% 0.55/0.75      inference('sup+', [status(thm)], ['86', '94'])).
% 0.55/0.75  thf('96', plain, (((sk_C_2) != (sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('97', plain, ($false),
% 0.55/0.75      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.61/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
