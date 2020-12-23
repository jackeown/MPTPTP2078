%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wVJ3DMvOMW

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:21 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 156 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  627 (1222 expanded)
%              Number of equality atoms :   29 (  65 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_xboole_0 @ X29 @ X30 )
      | ( ( k3_xboole_0 @ X29 @ ( k2_xboole_0 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_B )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_D_1 @ sk_B ),
    inference(clc,[status(thm)],['32','35'])).

thf('37',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    $false ),
    inference('sup-',[status(thm)],['41','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wVJ3DMvOMW
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.41/2.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.41/2.62  % Solved by: fo/fo7.sh
% 2.41/2.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.41/2.62  % done 2890 iterations in 2.160s
% 2.41/2.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.41/2.62  % SZS output start Refutation
% 2.41/2.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.41/2.62  thf(sk_B_type, type, sk_B: $i).
% 2.41/2.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.41/2.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.41/2.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.41/2.62  thf(sk_A_type, type, sk_A: $i).
% 2.41/2.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.41/2.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.41/2.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.41/2.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.41/2.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.41/2.62  thf(l27_zfmisc_1, axiom,
% 2.41/2.62    (![A:$i,B:$i]:
% 2.41/2.62     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.41/2.62  thf('0', plain,
% 2.41/2.62      (![X38 : $i, X39 : $i]:
% 2.41/2.62         ((r1_xboole_0 @ (k1_tarski @ X38) @ X39) | (r2_hidden @ X38 @ X39))),
% 2.41/2.62      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.41/2.62  thf(symmetry_r1_xboole_0, axiom,
% 2.41/2.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.41/2.62  thf('1', plain,
% 2.41/2.62      (![X10 : $i, X11 : $i]:
% 2.41/2.62         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 2.41/2.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.41/2.62  thf('2', plain,
% 2.41/2.62      (![X0 : $i, X1 : $i]:
% 2.41/2.62         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 2.41/2.62      inference('sup-', [status(thm)], ['0', '1'])).
% 2.41/2.62  thf(t149_zfmisc_1, conjecture,
% 2.41/2.62    (![A:$i,B:$i,C:$i,D:$i]:
% 2.41/2.62     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.41/2.62         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.41/2.62       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.41/2.62  thf(zf_stmt_0, negated_conjecture,
% 2.41/2.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.41/2.62        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.41/2.62            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.41/2.62          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.41/2.62    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.41/2.62  thf('3', plain,
% 2.41/2.62      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 2.41/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.62  thf(t12_xboole_1, axiom,
% 2.41/2.62    (![A:$i,B:$i]:
% 2.41/2.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.41/2.62  thf('4', plain,
% 2.41/2.62      (![X16 : $i, X17 : $i]:
% 2.41/2.62         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 2.41/2.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.41/2.62  thf('5', plain,
% 2.41/2.62      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))
% 2.41/2.62         = (k1_tarski @ sk_D_1))),
% 2.41/2.62      inference('sup-', [status(thm)], ['3', '4'])).
% 2.41/2.62  thf(commutativity_k2_xboole_0, axiom,
% 2.41/2.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.41/2.62  thf('6', plain,
% 2.41/2.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.41/2.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.41/2.62  thf('7', plain,
% 2.41/2.62      (((k2_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_B))
% 2.41/2.62         = (k1_tarski @ sk_D_1))),
% 2.41/2.62      inference('demod', [status(thm)], ['5', '6'])).
% 2.41/2.62  thf('8', plain,
% 2.41/2.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.41/2.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.41/2.62  thf(t70_xboole_1, axiom,
% 2.41/2.62    (![A:$i,B:$i,C:$i]:
% 2.41/2.62     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.41/2.62            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.41/2.62       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.41/2.62            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.41/2.62  thf('9', plain,
% 2.41/2.62      (![X25 : $i, X26 : $i, X28 : $i]:
% 2.41/2.62         ((r1_xboole_0 @ X25 @ X26)
% 2.41/2.62          | ~ (r1_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X28)))),
% 2.41/2.62      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.41/2.62  thf('10', plain,
% 2.41/2.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.62         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.41/2.62          | (r1_xboole_0 @ X2 @ X0))),
% 2.41/2.62      inference('sup-', [status(thm)], ['8', '9'])).
% 2.41/2.62  thf('11', plain,
% 2.41/2.62      (![X0 : $i]:
% 2.41/2.62         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_D_1))
% 2.41/2.62          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.41/2.62      inference('sup-', [status(thm)], ['7', '10'])).
% 2.41/2.62  thf(commutativity_k3_xboole_0, axiom,
% 2.41/2.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.41/2.62  thf('12', plain,
% 2.41/2.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.41/2.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.41/2.62  thf('13', plain,
% 2.41/2.62      (![X0 : $i]:
% 2.41/2.62         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_D_1))
% 2.41/2.62          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 2.41/2.62      inference('demod', [status(thm)], ['11', '12'])).
% 2.41/2.62  thf('14', plain,
% 2.41/2.62      (![X0 : $i]:
% 2.41/2.62         ((r2_hidden @ sk_D_1 @ X0)
% 2.41/2.62          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 2.41/2.62      inference('sup-', [status(thm)], ['2', '13'])).
% 2.41/2.62  thf('15', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.41/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.62  thf('16', plain,
% 2.41/2.62      (![X10 : $i, X11 : $i]:
% 2.41/2.62         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 2.41/2.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.41/2.62  thf('17', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.41/2.62      inference('sup-', [status(thm)], ['15', '16'])).
% 2.41/2.62  thf(t78_xboole_1, axiom,
% 2.41/2.62    (![A:$i,B:$i,C:$i]:
% 2.41/2.62     ( ( r1_xboole_0 @ A @ B ) =>
% 2.41/2.62       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 2.41/2.62         ( k3_xboole_0 @ A @ C ) ) ))).
% 2.41/2.62  thf('18', plain,
% 2.41/2.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.41/2.62         (~ (r1_xboole_0 @ X29 @ X30)
% 2.41/2.62          | ((k3_xboole_0 @ X29 @ (k2_xboole_0 @ X30 @ X31))
% 2.41/2.62              = (k3_xboole_0 @ X29 @ X31)))),
% 2.41/2.62      inference('cnf', [status(esa)], [t78_xboole_1])).
% 2.41/2.62  thf('19', plain,
% 2.41/2.62      (![X0 : $i]:
% 2.41/2.62         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))
% 2.41/2.62           = (k3_xboole_0 @ sk_B @ X0))),
% 2.41/2.62      inference('sup-', [status(thm)], ['17', '18'])).
% 2.41/2.62  thf(t4_xboole_0, axiom,
% 2.41/2.62    (![A:$i,B:$i]:
% 2.41/2.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.41/2.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.41/2.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.41/2.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.41/2.62  thf('20', plain,
% 2.41/2.62      (![X12 : $i, X13 : $i]:
% 2.41/2.62         ((r1_xboole_0 @ X12 @ X13)
% 2.41/2.62          | (r2_hidden @ (sk_C @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 2.41/2.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.41/2.62  thf('21', plain,
% 2.41/2.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.41/2.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.41/2.62  thf(t17_xboole_1, axiom,
% 2.41/2.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.41/2.62  thf('22', plain,
% 2.41/2.62      (![X21 : $i, X22 : $i]: (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ X21)),
% 2.41/2.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.41/2.62  thf(t28_xboole_1, axiom,
% 2.41/2.62    (![A:$i,B:$i]:
% 2.41/2.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.41/2.62  thf('23', plain,
% 2.41/2.62      (![X23 : $i, X24 : $i]:
% 2.41/2.62         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 2.41/2.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.41/2.62  thf('24', plain,
% 2.41/2.62      (![X0 : $i, X1 : $i]:
% 2.41/2.62         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 2.41/2.62           = (k3_xboole_0 @ X0 @ X1))),
% 2.41/2.63      inference('sup-', [status(thm)], ['22', '23'])).
% 2.41/2.63  thf('25', plain,
% 2.41/2.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.41/2.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.41/2.63  thf('26', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i]:
% 2.41/2.63         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.41/2.63           = (k3_xboole_0 @ X0 @ X1))),
% 2.41/2.63      inference('demod', [status(thm)], ['24', '25'])).
% 2.41/2.63  thf('27', plain,
% 2.41/2.63      (![X12 : $i, X14 : $i, X15 : $i]:
% 2.41/2.63         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 2.41/2.63          | ~ (r1_xboole_0 @ X12 @ X15))),
% 2.41/2.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.41/2.63  thf('28', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.41/2.63          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.63      inference('sup-', [status(thm)], ['26', '27'])).
% 2.41/2.63  thf('29', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.41/2.63          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.41/2.63      inference('sup-', [status(thm)], ['21', '28'])).
% 2.41/2.63  thf('30', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i]:
% 2.41/2.63         ((r1_xboole_0 @ X1 @ X0)
% 2.41/2.63          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.41/2.63      inference('sup-', [status(thm)], ['20', '29'])).
% 2.41/2.63  thf('31', plain,
% 2.41/2.63      (![X0 : $i]:
% 2.41/2.63         (~ (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ X0))
% 2.41/2.63          | (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ X0) @ sk_B))),
% 2.41/2.63      inference('sup-', [status(thm)], ['19', '30'])).
% 2.41/2.63  thf('32', plain,
% 2.41/2.63      (((r2_hidden @ sk_D_1 @ sk_B)
% 2.41/2.63        | (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B))),
% 2.41/2.63      inference('sup-', [status(thm)], ['14', '31'])).
% 2.41/2.63  thf('33', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.41/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.63  thf('34', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.41/2.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.41/2.63  thf('35', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 2.41/2.63      inference('demod', [status(thm)], ['33', '34'])).
% 2.41/2.63  thf('36', plain, ((r2_hidden @ sk_D_1 @ sk_B)),
% 2.41/2.63      inference('clc', [status(thm)], ['32', '35'])).
% 2.41/2.63  thf('37', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 2.41/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.41/2.63  thf(d4_xboole_0, axiom,
% 2.41/2.63    (![A:$i,B:$i,C:$i]:
% 2.41/2.63     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.41/2.63       ( ![D:$i]:
% 2.41/2.63         ( ( r2_hidden @ D @ C ) <=>
% 2.41/2.63           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.41/2.63  thf('38', plain,
% 2.41/2.63      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.41/2.63         (~ (r2_hidden @ X4 @ X5)
% 2.41/2.63          | ~ (r2_hidden @ X4 @ X6)
% 2.41/2.63          | (r2_hidden @ X4 @ X7)
% 2.41/2.63          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 2.41/2.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.41/2.63  thf('39', plain,
% 2.41/2.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.41/2.63         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 2.41/2.63          | ~ (r2_hidden @ X4 @ X6)
% 2.41/2.63          | ~ (r2_hidden @ X4 @ X5))),
% 2.41/2.63      inference('simplify', [status(thm)], ['38'])).
% 2.41/2.63  thf('40', plain,
% 2.41/2.63      (![X0 : $i]:
% 2.41/2.63         (~ (r2_hidden @ sk_D_1 @ X0)
% 2.41/2.63          | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ X0 @ sk_C_1)))),
% 2.41/2.63      inference('sup-', [status(thm)], ['37', '39'])).
% 2.41/2.63  thf('41', plain, ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 2.41/2.63      inference('sup-', [status(thm)], ['36', '40'])).
% 2.41/2.63  thf('42', plain,
% 2.41/2.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.41/2.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.41/2.63  thf('43', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.41/2.63      inference('sup-', [status(thm)], ['15', '16'])).
% 2.41/2.63  thf('44', plain,
% 2.41/2.63      (![X21 : $i, X22 : $i]: (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ X21)),
% 2.41/2.63      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.41/2.63  thf('45', plain,
% 2.41/2.63      (![X16 : $i, X17 : $i]:
% 2.41/2.63         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 2.41/2.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.41/2.63  thf('46', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i]:
% 2.41/2.63         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.41/2.63      inference('sup-', [status(thm)], ['44', '45'])).
% 2.41/2.63  thf('47', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.41/2.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.41/2.63  thf('48', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i]:
% 2.41/2.63         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 2.41/2.63      inference('demod', [status(thm)], ['46', '47'])).
% 2.41/2.63  thf('49', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.63         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.41/2.63          | (r1_xboole_0 @ X2 @ X0))),
% 2.41/2.63      inference('sup-', [status(thm)], ['8', '9'])).
% 2.41/2.63  thf('50', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.63         (~ (r1_xboole_0 @ X2 @ X0)
% 2.41/2.63          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.41/2.63      inference('sup-', [status(thm)], ['48', '49'])).
% 2.41/2.63  thf('51', plain,
% 2.41/2.63      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0))),
% 2.41/2.63      inference('sup-', [status(thm)], ['43', '50'])).
% 2.41/2.63  thf('52', plain,
% 2.41/2.63      (![X10 : $i, X11 : $i]:
% 2.41/2.63         ((r1_xboole_0 @ X10 @ X11) | ~ (r1_xboole_0 @ X11 @ X10))),
% 2.41/2.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.41/2.63  thf('53', plain,
% 2.41/2.63      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 2.41/2.63      inference('sup-', [status(thm)], ['51', '52'])).
% 2.41/2.63  thf('54', plain,
% 2.41/2.63      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_1) @ sk_B)),
% 2.41/2.63      inference('sup+', [status(thm)], ['42', '53'])).
% 2.41/2.63  thf('55', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.63         (~ (r1_xboole_0 @ X2 @ X0)
% 2.41/2.63          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.41/2.63      inference('sup-', [status(thm)], ['48', '49'])).
% 2.41/2.63  thf('56', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i]:
% 2.41/2.63         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_1) @ (k3_xboole_0 @ sk_B @ X1))),
% 2.41/2.63      inference('sup-', [status(thm)], ['54', '55'])).
% 2.41/2.63  thf('57', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i]:
% 2.41/2.63         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.41/2.63           = (k3_xboole_0 @ X0 @ X1))),
% 2.41/2.63      inference('demod', [status(thm)], ['24', '25'])).
% 2.41/2.63  thf('58', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.41/2.63          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.41/2.63      inference('sup-', [status(thm)], ['21', '28'])).
% 2.41/2.63  thf('59', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.41/2.63          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 2.41/2.63               (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 2.41/2.63      inference('sup-', [status(thm)], ['57', '58'])).
% 2.41/2.63  thf('60', plain,
% 2.41/2.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.41/2.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.41/2.63  thf('61', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i]:
% 2.41/2.63         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.41/2.63           = (k3_xboole_0 @ X0 @ X1))),
% 2.41/2.63      inference('demod', [status(thm)], ['24', '25'])).
% 2.41/2.63  thf('62', plain,
% 2.41/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.41/2.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.41/2.63          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.41/2.63      inference('demod', [status(thm)], ['59', '60', '61'])).
% 2.41/2.63  thf('63', plain,
% 2.41/2.63      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 2.41/2.63      inference('sup-', [status(thm)], ['56', '62'])).
% 2.41/2.63  thf('64', plain, ($false), inference('sup-', [status(thm)], ['41', '63'])).
% 2.41/2.63  
% 2.41/2.63  % SZS output end Refutation
% 2.41/2.63  
% 2.41/2.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
