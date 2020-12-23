%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ix5WzWLUy4

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:31 EST 2020

% Result     : Theorem 7.92s
% Output     : Refutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 214 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :   20
%              Number of atoms          :  887 (1689 expanded)
%              Number of equality atoms :   67 ( 129 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X1 @ X2 ) ) )
      = ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k4_xboole_0 @ X32 @ ( k1_tarski @ X33 ) )
        = X32 )
      | ( r2_hidden @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ X23 )
      | ( ( k4_xboole_0 @ X21 @ X23 )
       != X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('42',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('43',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('48',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','69'])).

thf('71',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30','33','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','75'])).

thf('77',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('82',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('85',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) ) @ X25 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','92'])).

thf('94',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('95',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ix5WzWLUy4
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:30:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 7.92/8.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.92/8.17  % Solved by: fo/fo7.sh
% 7.92/8.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.92/8.17  % done 6712 iterations in 7.708s
% 7.92/8.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.92/8.17  % SZS output start Refutation
% 7.92/8.17  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.92/8.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.92/8.17  thf(sk_A_type, type, sk_A: $i).
% 7.92/8.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.92/8.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.92/8.17  thf(sk_B_type, type, sk_B: $i).
% 7.92/8.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.92/8.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.92/8.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.92/8.17  thf(sk_D_type, type, sk_D: $i).
% 7.92/8.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.92/8.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.92/8.17  thf(t149_zfmisc_1, conjecture,
% 7.92/8.17    (![A:$i,B:$i,C:$i,D:$i]:
% 7.92/8.17     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 7.92/8.17         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 7.92/8.17       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 7.92/8.17  thf(zf_stmt_0, negated_conjecture,
% 7.92/8.17    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 7.92/8.17        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 7.92/8.17            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 7.92/8.17          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 7.92/8.17    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 7.92/8.17  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 7.92/8.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.92/8.17  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 7.92/8.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.92/8.17  thf(symmetry_r1_xboole_0, axiom,
% 7.92/8.17    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 7.92/8.17  thf('2', plain,
% 7.92/8.17      (![X2 : $i, X3 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 7.92/8.17      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 7.92/8.17  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 7.92/8.17      inference('sup-', [status(thm)], ['1', '2'])).
% 7.92/8.17  thf('4', plain,
% 7.92/8.17      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 7.92/8.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.92/8.17  thf(commutativity_k3_xboole_0, axiom,
% 7.92/8.17    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.92/8.17  thf('5', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.92/8.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.92/8.17  thf('6', plain,
% 7.92/8.17      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 7.92/8.17      inference('demod', [status(thm)], ['4', '5'])).
% 7.92/8.17  thf(t28_xboole_1, axiom,
% 7.92/8.17    (![A:$i,B:$i]:
% 7.92/8.17     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.92/8.17  thf('7', plain,
% 7.92/8.17      (![X11 : $i, X12 : $i]:
% 7.92/8.17         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 7.92/8.17      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.92/8.17  thf('8', plain,
% 7.92/8.17      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 7.92/8.17         = (k3_xboole_0 @ sk_B @ sk_A))),
% 7.92/8.17      inference('sup-', [status(thm)], ['6', '7'])).
% 7.92/8.17  thf('9', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.92/8.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.92/8.17  thf('10', plain,
% 7.92/8.17      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 7.92/8.17         = (k3_xboole_0 @ sk_B @ sk_A))),
% 7.92/8.17      inference('demod', [status(thm)], ['8', '9'])).
% 7.92/8.17  thf(t16_xboole_1, axiom,
% 7.92/8.17    (![A:$i,B:$i,C:$i]:
% 7.92/8.17     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 7.92/8.17       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 7.92/8.17  thf('11', plain,
% 7.92/8.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 7.92/8.17           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 7.92/8.17      inference('cnf', [status(esa)], [t16_xboole_1])).
% 7.92/8.17  thf('12', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.92/8.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.92/8.17  thf('13', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 7.92/8.17           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['11', '12'])).
% 7.92/8.17  thf('14', plain,
% 7.92/8.17      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))
% 7.92/8.17         = (k3_xboole_0 @ sk_B @ sk_A))),
% 7.92/8.17      inference('demod', [status(thm)], ['10', '13'])).
% 7.92/8.17  thf('15', plain,
% 7.92/8.17      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 7.92/8.17         = (k3_xboole_0 @ sk_B @ sk_A))),
% 7.92/8.17      inference('demod', [status(thm)], ['8', '9'])).
% 7.92/8.17  thf('16', plain,
% 7.92/8.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 7.92/8.17           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 7.92/8.17      inference('cnf', [status(esa)], [t16_xboole_1])).
% 7.92/8.17  thf('17', plain,
% 7.92/8.17      (![X0 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 7.92/8.17           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ 
% 7.92/8.17              (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['15', '16'])).
% 7.92/8.17  thf('18', plain,
% 7.92/8.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 7.92/8.17           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 7.92/8.17      inference('cnf', [status(esa)], [t16_xboole_1])).
% 7.92/8.17  thf('19', plain,
% 7.92/8.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 7.92/8.17           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 7.92/8.17      inference('cnf', [status(esa)], [t16_xboole_1])).
% 7.92/8.17  thf('20', plain,
% 7.92/8.17      (![X0 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 7.92/8.17           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ 
% 7.92/8.17              (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))))),
% 7.92/8.17      inference('demod', [status(thm)], ['17', '18', '19'])).
% 7.92/8.17  thf('21', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 7.92/8.17           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['11', '12'])).
% 7.92/8.17  thf('22', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.92/8.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.92/8.17  thf('23', plain,
% 7.92/8.17      (![X8 : $i, X9 : $i, X10 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 7.92/8.17           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 7.92/8.17      inference('cnf', [status(esa)], [t16_xboole_1])).
% 7.92/8.17  thf('24', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 7.92/8.17           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['22', '23'])).
% 7.92/8.17  thf('25', plain,
% 7.92/8.17      (![X0 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 7.92/8.17           = (k3_xboole_0 @ sk_B @ 
% 7.92/8.17              (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))))),
% 7.92/8.17      inference('demod', [status(thm)], ['20', '21', '24'])).
% 7.92/8.17  thf('26', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 7.92/8.17           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['22', '23'])).
% 7.92/8.17  thf('27', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 7.92/8.17           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['11', '12'])).
% 7.92/8.17  thf('28', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X1 @ X2)))
% 7.92/8.17           = (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 7.92/8.17      inference('sup+', [status(thm)], ['26', '27'])).
% 7.92/8.17  thf('29', plain,
% 7.92/8.17      (![X0 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 7.92/8.17           = (k3_xboole_0 @ X0 @ 
% 7.92/8.17              (k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 7.92/8.17      inference('sup+', [status(thm)], ['25', '28'])).
% 7.92/8.17  thf('30', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.92/8.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.92/8.17  thf('31', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.92/8.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.92/8.17  thf('32', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 7.92/8.17           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['11', '12'])).
% 7.92/8.17  thf('33', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 7.92/8.17           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['31', '32'])).
% 7.92/8.17  thf(t65_zfmisc_1, axiom,
% 7.92/8.17    (![A:$i,B:$i]:
% 7.92/8.17     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 7.92/8.17       ( ~( r2_hidden @ B @ A ) ) ))).
% 7.92/8.17  thf('34', plain,
% 7.92/8.17      (![X32 : $i, X33 : $i]:
% 7.92/8.17         (((k4_xboole_0 @ X32 @ (k1_tarski @ X33)) = (X32))
% 7.92/8.17          | (r2_hidden @ X33 @ X32))),
% 7.92/8.17      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 7.92/8.17  thf(t83_xboole_1, axiom,
% 7.92/8.17    (![A:$i,B:$i]:
% 7.92/8.17     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.92/8.17  thf('35', plain,
% 7.92/8.17      (![X21 : $i, X23 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X21 @ X23) | ((k4_xboole_0 @ X21 @ X23) != (X21)))),
% 7.92/8.17      inference('cnf', [status(esa)], [t83_xboole_1])).
% 7.92/8.17  thf('36', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]:
% 7.92/8.17         (((X0) != (X0))
% 7.92/8.17          | (r2_hidden @ X1 @ X0)
% 7.92/8.17          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 7.92/8.17      inference('sup-', [status(thm)], ['34', '35'])).
% 7.92/8.17  thf('37', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 7.92/8.17      inference('simplify', [status(thm)], ['36'])).
% 7.92/8.17  thf('38', plain,
% 7.92/8.17      (![X2 : $i, X3 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 7.92/8.17      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 7.92/8.17  thf('39', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]:
% 7.92/8.17         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 7.92/8.17      inference('sup-', [status(thm)], ['37', '38'])).
% 7.92/8.17  thf(t70_xboole_1, axiom,
% 7.92/8.17    (![A:$i,B:$i,C:$i]:
% 7.92/8.17     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 7.92/8.17            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 7.92/8.17       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 7.92/8.17            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 7.92/8.17  thf('40', plain,
% 7.92/8.17      (![X17 : $i, X18 : $i, X20 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X17 @ X18)
% 7.92/8.17          | ~ (r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X20)))),
% 7.92/8.17      inference('cnf', [status(esa)], [t70_xboole_1])).
% 7.92/8.17  thf('41', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.92/8.17         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 7.92/8.17          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 7.92/8.17      inference('sup-', [status(thm)], ['39', '40'])).
% 7.92/8.17  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 7.92/8.17  thf('42', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 7.92/8.17      inference('cnf', [status(esa)], [t65_xboole_1])).
% 7.92/8.17  thf('43', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 7.92/8.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.92/8.17  thf('44', plain,
% 7.92/8.17      (![X17 : $i, X18 : $i, X19 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 7.92/8.17          | ~ (r1_xboole_0 @ X17 @ X18)
% 7.92/8.17          | ~ (r1_xboole_0 @ X17 @ X19))),
% 7.92/8.17      inference('cnf', [status(esa)], [t70_xboole_1])).
% 7.92/8.17  thf('45', plain,
% 7.92/8.17      (![X0 : $i]:
% 7.92/8.17         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 7.92/8.17          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 7.92/8.17      inference('sup-', [status(thm)], ['43', '44'])).
% 7.92/8.17  thf('46', plain,
% 7.92/8.17      ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 7.92/8.17      inference('sup-', [status(thm)], ['42', '45'])).
% 7.92/8.17  thf('47', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 7.92/8.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.92/8.17  thf(t3_xboole_0, axiom,
% 7.92/8.17    (![A:$i,B:$i]:
% 7.92/8.17     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 7.92/8.17            ( r1_xboole_0 @ A @ B ) ) ) & 
% 7.92/8.17       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 7.92/8.17            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 7.92/8.17  thf('48', plain,
% 7.92/8.17      (![X4 : $i, X6 : $i, X7 : $i]:
% 7.92/8.17         (~ (r2_hidden @ X6 @ X4)
% 7.92/8.17          | ~ (r2_hidden @ X6 @ X7)
% 7.92/8.17          | ~ (r1_xboole_0 @ X4 @ X7))),
% 7.92/8.17      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.92/8.17  thf('49', plain,
% 7.92/8.17      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 7.92/8.17      inference('sup-', [status(thm)], ['47', '48'])).
% 7.92/8.17  thf('50', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 7.92/8.17      inference('sup-', [status(thm)], ['46', '49'])).
% 7.92/8.17  thf('51', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 7.92/8.17      inference('sup-', [status(thm)], ['41', '50'])).
% 7.92/8.17  thf('52', plain,
% 7.92/8.17      (![X2 : $i, X3 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 7.92/8.17      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 7.92/8.17  thf('53', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 7.92/8.17      inference('sup-', [status(thm)], ['51', '52'])).
% 7.92/8.17  thf('54', plain,
% 7.92/8.17      (![X21 : $i, X22 : $i]:
% 7.92/8.17         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 7.92/8.17      inference('cnf', [status(esa)], [t83_xboole_1])).
% 7.92/8.17  thf('55', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 7.92/8.17      inference('sup-', [status(thm)], ['53', '54'])).
% 7.92/8.17  thf(t48_xboole_1, axiom,
% 7.92/8.17    (![A:$i,B:$i]:
% 7.92/8.17     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.92/8.17  thf('56', plain,
% 7.92/8.17      (![X14 : $i, X15 : $i]:
% 7.92/8.17         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 7.92/8.17           = (k3_xboole_0 @ X14 @ X15))),
% 7.92/8.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.92/8.17  thf('57', plain,
% 7.92/8.17      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['55', '56'])).
% 7.92/8.17  thf(t3_boole, axiom,
% 7.92/8.17    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.92/8.17  thf('58', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 7.92/8.17      inference('cnf', [status(esa)], [t3_boole])).
% 7.92/8.17  thf('59', plain,
% 7.92/8.17      (![X14 : $i, X15 : $i]:
% 7.92/8.17         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 7.92/8.17           = (k3_xboole_0 @ X14 @ X15))),
% 7.92/8.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.92/8.17  thf('60', plain,
% 7.92/8.17      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 7.92/8.17      inference('sup+', [status(thm)], ['58', '59'])).
% 7.92/8.17  thf('61', plain,
% 7.92/8.17      (![X14 : $i, X15 : $i]:
% 7.92/8.17         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 7.92/8.17           = (k3_xboole_0 @ X14 @ X15))),
% 7.92/8.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.92/8.17  thf('62', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 7.92/8.17      inference('cnf', [status(esa)], [t65_xboole_1])).
% 7.92/8.17  thf('63', plain,
% 7.92/8.17      (![X2 : $i, X3 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 7.92/8.17      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 7.92/8.17  thf('64', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 7.92/8.17      inference('sup-', [status(thm)], ['62', '63'])).
% 7.92/8.17  thf('65', plain,
% 7.92/8.17      (![X21 : $i, X22 : $i]:
% 7.92/8.17         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 7.92/8.17      inference('cnf', [status(esa)], [t83_xboole_1])).
% 7.92/8.17  thf('66', plain,
% 7.92/8.17      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 7.92/8.17      inference('sup-', [status(thm)], ['64', '65'])).
% 7.92/8.17  thf('67', plain,
% 7.92/8.17      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 7.92/8.17      inference('sup+', [status(thm)], ['61', '66'])).
% 7.92/8.17  thf('68', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.92/8.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.92/8.17  thf('69', plain,
% 7.92/8.17      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 7.92/8.17      inference('sup+', [status(thm)], ['67', '68'])).
% 7.92/8.17  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.92/8.17      inference('demod', [status(thm)], ['60', '69'])).
% 7.92/8.17  thf('71', plain,
% 7.92/8.17      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)))),
% 7.92/8.17      inference('demod', [status(thm)], ['57', '70'])).
% 7.92/8.17  thf('72', plain,
% 7.92/8.17      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 7.92/8.17      inference('sup+', [status(thm)], ['67', '68'])).
% 7.92/8.17  thf('73', plain,
% 7.92/8.17      (![X0 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 7.92/8.17           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 7.92/8.17      inference('demod', [status(thm)], ['29', '30', '33', '71', '72'])).
% 7.92/8.17  thf('74', plain,
% 7.92/8.17      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 7.92/8.17      inference('sup+', [status(thm)], ['67', '68'])).
% 7.92/8.17  thf('75', plain,
% 7.92/8.17      (![X0 : $i]:
% 7.92/8.17         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 7.92/8.17      inference('demod', [status(thm)], ['73', '74'])).
% 7.92/8.17  thf('76', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 7.92/8.17      inference('demod', [status(thm)], ['14', '75'])).
% 7.92/8.17  thf('77', plain,
% 7.92/8.17      (![X14 : $i, X15 : $i]:
% 7.92/8.17         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 7.92/8.17           = (k3_xboole_0 @ X14 @ X15))),
% 7.92/8.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.92/8.17  thf('78', plain,
% 7.92/8.17      (![X14 : $i, X15 : $i]:
% 7.92/8.17         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 7.92/8.17           = (k3_xboole_0 @ X14 @ X15))),
% 7.92/8.17      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.92/8.17  thf('79', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]:
% 7.92/8.17         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 7.92/8.17           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['77', '78'])).
% 7.92/8.17  thf('80', plain,
% 7.92/8.17      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 7.92/8.17         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['76', '79'])).
% 7.92/8.17  thf('81', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 7.92/8.17      inference('cnf', [status(esa)], [t3_boole])).
% 7.92/8.17  thf('82', plain,
% 7.92/8.17      (((sk_B) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 7.92/8.17      inference('demod', [status(thm)], ['80', '81'])).
% 7.92/8.17  thf('83', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.92/8.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.92/8.17  thf('84', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.92/8.17      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.92/8.17  thf(t90_xboole_1, axiom,
% 7.92/8.17    (![A:$i,B:$i]:
% 7.92/8.17     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 7.92/8.17  thf('85', plain,
% 7.92/8.17      (![X24 : $i, X25 : $i]:
% 7.92/8.17         (r1_xboole_0 @ (k4_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)) @ X25)),
% 7.92/8.17      inference('cnf', [status(esa)], [t90_xboole_1])).
% 7.92/8.17  thf('86', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]:
% 7.92/8.17         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X1)),
% 7.92/8.17      inference('sup+', [status(thm)], ['84', '85'])).
% 7.92/8.17  thf('87', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]:
% 7.92/8.17         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 7.92/8.17      inference('sup+', [status(thm)], ['83', '86'])).
% 7.92/8.17  thf('88', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]:
% 7.92/8.17         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 7.92/8.17           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 7.92/8.17      inference('sup+', [status(thm)], ['77', '78'])).
% 7.92/8.17  thf('89', plain,
% 7.92/8.17      (![X0 : $i, X1 : $i]:
% 7.92/8.17         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 7.92/8.17      inference('demod', [status(thm)], ['87', '88'])).
% 7.92/8.17  thf('90', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 7.92/8.17      inference('sup+', [status(thm)], ['82', '89'])).
% 7.92/8.17  thf('91', plain,
% 7.92/8.17      (![X17 : $i, X18 : $i, X19 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 7.92/8.17          | ~ (r1_xboole_0 @ X17 @ X18)
% 7.92/8.17          | ~ (r1_xboole_0 @ X17 @ X19))),
% 7.92/8.17      inference('cnf', [status(esa)], [t70_xboole_1])).
% 7.92/8.17  thf('92', plain,
% 7.92/8.17      (![X0 : $i]:
% 7.92/8.17         (~ (r1_xboole_0 @ sk_B @ X0)
% 7.92/8.17          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 7.92/8.17      inference('sup-', [status(thm)], ['90', '91'])).
% 7.92/8.17  thf('93', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 7.92/8.17      inference('sup-', [status(thm)], ['3', '92'])).
% 7.92/8.17  thf('94', plain,
% 7.92/8.17      (![X2 : $i, X3 : $i]:
% 7.92/8.17         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 7.92/8.17      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 7.92/8.17  thf('95', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 7.92/8.17      inference('sup-', [status(thm)], ['93', '94'])).
% 7.92/8.17  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 7.92/8.17  
% 7.92/8.17  % SZS output end Refutation
% 7.92/8.17  
% 7.92/8.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
