%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M0r3dLE4yE

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:20 EST 2020

% Result     : Theorem 1.08s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 134 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  804 (1135 expanded)
%              Number of equality atoms :  103 ( 129 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X35
        = ( k1_enumset1 @ X32 @ X33 @ X34 ) )
      | ( X35
        = ( k2_tarski @ X32 @ X34 ) )
      | ( X35
        = ( k2_tarski @ X33 @ X34 ) )
      | ( X35
        = ( k2_tarski @ X32 @ X33 ) )
      | ( X35
        = ( k1_tarski @ X34 ) )
      | ( X35
        = ( k1_tarski @ X33 ) )
      | ( X35
        = ( k1_tarski @ X32 ) )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('32',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
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

thf('50',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','53'])).

thf('55',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ( r2_hidden @ X21 @ X22 )
      | ( X22
       != ( k2_tarski @ X23 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('57',plain,(
    ! [X20: $i,X23: $i] :
      ( r2_hidden @ X20 @ ( k2_tarski @ X23 @ X20 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','58'])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('61',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['62'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X17 @ X18 )
      | ( ( k3_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['2','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M0r3dLE4yE
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.08/1.30  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.08/1.30  % Solved by: fo/fo7.sh
% 1.08/1.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.08/1.30  % done 1673 iterations in 0.850s
% 1.08/1.30  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.08/1.30  % SZS output start Refutation
% 1.08/1.30  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.08/1.30  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.08/1.30  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.08/1.30  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.08/1.30  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.08/1.30  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.08/1.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.08/1.30  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.08/1.30  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.08/1.30  thf(sk_A_type, type, sk_A: $i).
% 1.08/1.30  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.08/1.30  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.08/1.30  thf(sk_B_type, type, sk_B: $i).
% 1.08/1.30  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.08/1.30  thf(t149_zfmisc_1, conjecture,
% 1.08/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.08/1.30     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.08/1.30         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.08/1.30       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.08/1.30  thf(zf_stmt_0, negated_conjecture,
% 1.08/1.30    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.08/1.30        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.08/1.30            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.08/1.30          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.08/1.30    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.08/1.30  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.08/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.30  thf(commutativity_k2_xboole_0, axiom,
% 1.08/1.30    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.08/1.30  thf('1', plain,
% 1.08/1.30      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.08/1.30      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.08/1.30  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 1.08/1.30      inference('demod', [status(thm)], ['0', '1'])).
% 1.08/1.30  thf('3', plain,
% 1.08/1.30      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 1.08/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.30  thf(commutativity_k3_xboole_0, axiom,
% 1.08/1.30    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.08/1.30  thf('4', plain,
% 1.08/1.30      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.08/1.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.30  thf('5', plain,
% 1.08/1.30      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 1.08/1.30      inference('demod', [status(thm)], ['3', '4'])).
% 1.08/1.30  thf(t71_enumset1, axiom,
% 1.08/1.30    (![A:$i,B:$i,C:$i]:
% 1.08/1.30     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.08/1.30  thf('6', plain,
% 1.08/1.30      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.08/1.30         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 1.08/1.30           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 1.08/1.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.08/1.30  thf(t70_enumset1, axiom,
% 1.08/1.30    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.08/1.30  thf('7', plain,
% 1.08/1.30      (![X27 : $i, X28 : $i]:
% 1.08/1.30         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 1.08/1.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.08/1.30  thf('8', plain,
% 1.08/1.30      (![X0 : $i, X1 : $i]:
% 1.08/1.30         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.08/1.30      inference('sup+', [status(thm)], ['6', '7'])).
% 1.08/1.30  thf(t69_enumset1, axiom,
% 1.08/1.30    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.08/1.30  thf('9', plain, (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.08/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.08/1.30  thf('10', plain,
% 1.08/1.30      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.08/1.30      inference('sup+', [status(thm)], ['8', '9'])).
% 1.08/1.30  thf('11', plain,
% 1.08/1.30      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.08/1.30         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 1.08/1.30           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 1.08/1.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.08/1.30  thf(t142_zfmisc_1, axiom,
% 1.08/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.08/1.30     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.08/1.30       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 1.08/1.30            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 1.08/1.30            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 1.08/1.30            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 1.08/1.30            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 1.08/1.30            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 1.08/1.30  thf('12', plain,
% 1.08/1.30      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.08/1.30         (((X35) = (k1_enumset1 @ X32 @ X33 @ X34))
% 1.08/1.30          | ((X35) = (k2_tarski @ X32 @ X34))
% 1.08/1.30          | ((X35) = (k2_tarski @ X33 @ X34))
% 1.08/1.30          | ((X35) = (k2_tarski @ X32 @ X33))
% 1.08/1.30          | ((X35) = (k1_tarski @ X34))
% 1.08/1.30          | ((X35) = (k1_tarski @ X33))
% 1.08/1.30          | ((X35) = (k1_tarski @ X32))
% 1.08/1.30          | ((X35) = (k1_xboole_0))
% 1.08/1.30          | ~ (r1_tarski @ X35 @ (k1_enumset1 @ X32 @ X33 @ X34)))),
% 1.08/1.30      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 1.08/1.30  thf('13', plain,
% 1.08/1.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.08/1.30         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 1.08/1.30          | ((X3) = (k1_xboole_0))
% 1.08/1.30          | ((X3) = (k1_tarski @ X2))
% 1.08/1.30          | ((X3) = (k1_tarski @ X1))
% 1.08/1.30          | ((X3) = (k1_tarski @ X0))
% 1.08/1.30          | ((X3) = (k2_tarski @ X2 @ X1))
% 1.08/1.30          | ((X3) = (k2_tarski @ X1 @ X0))
% 1.08/1.30          | ((X3) = (k2_tarski @ X2 @ X0))
% 1.08/1.30          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.08/1.30      inference('sup-', [status(thm)], ['11', '12'])).
% 1.08/1.30  thf('14', plain,
% 1.08/1.30      (![X0 : $i, X1 : $i]:
% 1.08/1.30         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 1.08/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.08/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.08/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_xboole_0)))),
% 1.08/1.30      inference('sup-', [status(thm)], ['10', '13'])).
% 1.08/1.30  thf('15', plain,
% 1.08/1.30      (![X27 : $i, X28 : $i]:
% 1.08/1.30         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 1.08/1.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.08/1.30  thf('16', plain,
% 1.08/1.30      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.08/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.08/1.30  thf('17', plain,
% 1.08/1.30      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.08/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.08/1.30  thf('18', plain,
% 1.08/1.30      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.08/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.08/1.30  thf('19', plain,
% 1.08/1.30      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.08/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.08/1.30  thf('20', plain,
% 1.08/1.30      (![X0 : $i, X1 : $i]:
% 1.08/1.30         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ((X1) = (k1_xboole_0)))),
% 1.08/1.30      inference('demod', [status(thm)], ['14', '15', '16', '17', '18', '19'])).
% 1.08/1.30  thf('21', plain,
% 1.08/1.30      (![X0 : $i, X1 : $i]:
% 1.08/1.30         (((X1) = (k1_xboole_0))
% 1.08/1.30          | ((X1) = (k1_tarski @ X0))
% 1.08/1.30          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 1.08/1.30      inference('simplify', [status(thm)], ['20'])).
% 1.08/1.30  thf('22', plain,
% 1.08/1.30      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D_1))
% 1.08/1.30        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.08/1.30      inference('sup-', [status(thm)], ['5', '21'])).
% 1.08/1.30  thf('23', plain,
% 1.08/1.30      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.08/1.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.30  thf('24', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.08/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.30  thf(d7_xboole_0, axiom,
% 1.08/1.30    (![A:$i,B:$i]:
% 1.08/1.30     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.08/1.30       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.08/1.30  thf('25', plain,
% 1.08/1.30      (![X4 : $i, X5 : $i]:
% 1.08/1.30         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.08/1.30      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.08/1.30  thf('26', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.08/1.30      inference('sup-', [status(thm)], ['24', '25'])).
% 1.08/1.30  thf('27', plain,
% 1.08/1.30      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.08/1.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.30  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.08/1.30      inference('demod', [status(thm)], ['26', '27'])).
% 1.08/1.30  thf(t16_xboole_1, axiom,
% 1.08/1.30    (![A:$i,B:$i,C:$i]:
% 1.08/1.30     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.08/1.30       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.08/1.30  thf('29', plain,
% 1.08/1.30      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.08/1.30         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 1.08/1.30           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.08/1.30      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.08/1.30  thf('30', plain,
% 1.08/1.30      (![X0 : $i]:
% 1.08/1.30         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 1.08/1.30           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 1.08/1.30      inference('sup+', [status(thm)], ['28', '29'])).
% 1.08/1.30  thf('31', plain,
% 1.08/1.30      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.08/1.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.30  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.08/1.30  thf('32', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 1.08/1.30      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.08/1.30  thf('33', plain,
% 1.08/1.30      (![X4 : $i, X5 : $i]:
% 1.08/1.30         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.08/1.30      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.08/1.30  thf('34', plain,
% 1.08/1.30      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.08/1.30      inference('sup-', [status(thm)], ['32', '33'])).
% 1.08/1.30  thf('35', plain,
% 1.08/1.30      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.08/1.30      inference('sup+', [status(thm)], ['31', '34'])).
% 1.08/1.30  thf('36', plain,
% 1.08/1.30      (![X0 : $i]:
% 1.08/1.30         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 1.08/1.30      inference('demod', [status(thm)], ['30', '35'])).
% 1.08/1.30  thf('37', plain,
% 1.08/1.30      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.08/1.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.30  thf('38', plain,
% 1.08/1.30      (![X4 : $i, X6 : $i]:
% 1.08/1.30         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.08/1.30      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.08/1.30  thf('39', plain,
% 1.08/1.30      (![X0 : $i, X1 : $i]:
% 1.08/1.30         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.08/1.30      inference('sup-', [status(thm)], ['37', '38'])).
% 1.08/1.30  thf('40', plain,
% 1.08/1.30      (![X0 : $i]:
% 1.08/1.30         (((k1_xboole_0) != (k1_xboole_0))
% 1.08/1.30          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B))),
% 1.08/1.30      inference('sup-', [status(thm)], ['36', '39'])).
% 1.08/1.30  thf('41', plain,
% 1.08/1.30      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 1.08/1.30      inference('simplify', [status(thm)], ['40'])).
% 1.08/1.30  thf('42', plain,
% 1.08/1.30      (![X4 : $i, X5 : $i]:
% 1.08/1.30         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.08/1.30      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.08/1.30  thf('43', plain,
% 1.08/1.30      (![X0 : $i]:
% 1.08/1.30         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B) = (k1_xboole_0))),
% 1.08/1.30      inference('sup-', [status(thm)], ['41', '42'])).
% 1.08/1.30  thf('44', plain,
% 1.08/1.30      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.08/1.30         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 1.08/1.30           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.08/1.30      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.08/1.30  thf('45', plain,
% 1.08/1.30      (![X0 : $i]:
% 1.08/1.30         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 1.08/1.30      inference('demod', [status(thm)], ['43', '44'])).
% 1.08/1.30  thf('46', plain,
% 1.08/1.30      (![X4 : $i, X6 : $i]:
% 1.08/1.30         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.08/1.30      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.08/1.30  thf('47', plain,
% 1.08/1.30      (![X0 : $i]:
% 1.08/1.30         (((k1_xboole_0) != (k1_xboole_0))
% 1.08/1.30          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.08/1.30      inference('sup-', [status(thm)], ['45', '46'])).
% 1.08/1.30  thf('48', plain,
% 1.08/1.30      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.08/1.30      inference('simplify', [status(thm)], ['47'])).
% 1.08/1.30  thf('49', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 1.08/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.30  thf(t3_xboole_0, axiom,
% 1.08/1.30    (![A:$i,B:$i]:
% 1.08/1.30     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.08/1.30            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.08/1.30       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.08/1.30            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.08/1.30  thf('50', plain,
% 1.08/1.30      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.08/1.30         (~ (r2_hidden @ X11 @ X9)
% 1.08/1.30          | ~ (r2_hidden @ X11 @ X12)
% 1.08/1.30          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.08/1.30      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.08/1.30  thf('51', plain,
% 1.08/1.30      (![X0 : $i]:
% 1.08/1.30         (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 1.08/1.30      inference('sup-', [status(thm)], ['49', '50'])).
% 1.08/1.30  thf('52', plain,
% 1.08/1.30      (![X0 : $i]: ~ (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.08/1.30      inference('sup-', [status(thm)], ['48', '51'])).
% 1.08/1.30  thf('53', plain,
% 1.08/1.30      (![X0 : $i]: ~ (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 1.08/1.30      inference('sup-', [status(thm)], ['23', '52'])).
% 1.08/1.30  thf('54', plain,
% 1.08/1.30      ((~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1))
% 1.08/1.30        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.08/1.30      inference('sup-', [status(thm)], ['22', '53'])).
% 1.08/1.30  thf('55', plain,
% 1.08/1.30      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.08/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.08/1.30  thf(d2_tarski, axiom,
% 1.08/1.30    (![A:$i,B:$i,C:$i]:
% 1.08/1.30     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.08/1.30       ( ![D:$i]:
% 1.08/1.30         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.08/1.30  thf('56', plain,
% 1.08/1.30      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.08/1.30         (((X21) != (X20))
% 1.08/1.30          | (r2_hidden @ X21 @ X22)
% 1.08/1.30          | ((X22) != (k2_tarski @ X23 @ X20)))),
% 1.08/1.30      inference('cnf', [status(esa)], [d2_tarski])).
% 1.08/1.30  thf('57', plain,
% 1.08/1.30      (![X20 : $i, X23 : $i]: (r2_hidden @ X20 @ (k2_tarski @ X23 @ X20))),
% 1.08/1.30      inference('simplify', [status(thm)], ['56'])).
% 1.08/1.30  thf('58', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.08/1.30      inference('sup+', [status(thm)], ['55', '57'])).
% 1.08/1.30  thf('59', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.08/1.30      inference('demod', [status(thm)], ['54', '58'])).
% 1.08/1.30  thf('60', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.08/1.30      inference('demod', [status(thm)], ['26', '27'])).
% 1.08/1.30  thf('61', plain,
% 1.08/1.30      (![X4 : $i, X6 : $i]:
% 1.08/1.30         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.08/1.30      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.08/1.30  thf('62', plain,
% 1.08/1.30      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 1.08/1.30      inference('sup-', [status(thm)], ['60', '61'])).
% 1.08/1.30  thf('63', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.08/1.30      inference('simplify', [status(thm)], ['62'])).
% 1.08/1.30  thf(t78_xboole_1, axiom,
% 1.08/1.30    (![A:$i,B:$i,C:$i]:
% 1.08/1.30     ( ( r1_xboole_0 @ A @ B ) =>
% 1.08/1.30       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.08/1.30         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.08/1.30  thf('64', plain,
% 1.08/1.30      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.08/1.30         (~ (r1_xboole_0 @ X17 @ X18)
% 1.08/1.30          | ((k3_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 1.08/1.30              = (k3_xboole_0 @ X17 @ X19)))),
% 1.08/1.30      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.08/1.30  thf('65', plain,
% 1.08/1.30      (![X0 : $i]:
% 1.08/1.30         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))
% 1.08/1.30           = (k3_xboole_0 @ sk_B @ X0))),
% 1.08/1.30      inference('sup-', [status(thm)], ['63', '64'])).
% 1.08/1.30  thf('66', plain,
% 1.08/1.30      (![X0 : $i, X1 : $i]:
% 1.08/1.30         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.08/1.30      inference('sup-', [status(thm)], ['37', '38'])).
% 1.08/1.30  thf('67', plain,
% 1.08/1.30      (![X0 : $i]:
% 1.08/1.30         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.08/1.30          | (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ X0) @ sk_B))),
% 1.08/1.30      inference('sup-', [status(thm)], ['65', '66'])).
% 1.08/1.30  thf('68', plain,
% 1.08/1.30      ((((k1_xboole_0) != (k1_xboole_0))
% 1.08/1.30        | (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B))),
% 1.08/1.30      inference('sup-', [status(thm)], ['59', '67'])).
% 1.08/1.30  thf('69', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 1.08/1.30      inference('simplify', [status(thm)], ['68'])).
% 1.08/1.30  thf('70', plain, ($false), inference('demod', [status(thm)], ['2', '69'])).
% 1.08/1.30  
% 1.08/1.30  % SZS output end Refutation
% 1.08/1.30  
% 1.08/1.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
