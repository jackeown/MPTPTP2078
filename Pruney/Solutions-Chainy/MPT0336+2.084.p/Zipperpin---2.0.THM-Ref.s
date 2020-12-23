%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Of6Xi8xYIv

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:31 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 282 expanded)
%              Number of leaves         :   24 (  99 expanded)
%              Depth                    :   22
%              Number of atoms          :  631 (2119 expanded)
%              Number of equality atoms :   32 ( 107 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) )
        = X34 )
      | ( r2_hidden @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ ( k2_xboole_0 @ sk_B @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['19','48'])).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('51',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['6','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('56',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['58','63'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('73',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Of6Xi8xYIv
% 0.14/0.38  % Computer   : n018.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 13:50:27 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.72/1.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.92  % Solved by: fo/fo7.sh
% 1.72/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.92  % done 5324 iterations in 1.448s
% 1.72/1.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.92  % SZS output start Refutation
% 1.72/1.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.72/1.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.72/1.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.92  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.72/1.92  thf(sk_D_type, type, sk_D: $i).
% 1.72/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.72/1.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.72/1.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.72/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.72/1.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.72/1.92  thf(t149_zfmisc_1, conjecture,
% 1.72/1.92    (![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.92     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.72/1.92         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.72/1.92       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.72/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.92    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.72/1.92        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.72/1.92            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.72/1.92          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.72/1.92    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.72/1.92  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(symmetry_r1_xboole_0, axiom,
% 1.72/1.92    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.72/1.92  thf('2', plain,
% 1.72/1.92      (![X2 : $i, X3 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.72/1.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.72/1.92  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.72/1.92      inference('sup-', [status(thm)], ['1', '2'])).
% 1.72/1.92  thf('4', plain,
% 1.72/1.92      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(commutativity_k3_xboole_0, axiom,
% 1.72/1.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.72/1.92  thf('5', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.72/1.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.72/1.92  thf('6', plain,
% 1.72/1.92      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.72/1.92      inference('demod', [status(thm)], ['4', '5'])).
% 1.72/1.92  thf(t65_zfmisc_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.72/1.92       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.72/1.92  thf('7', plain,
% 1.72/1.92      (![X34 : $i, X35 : $i]:
% 1.72/1.92         (((k4_xboole_0 @ X34 @ (k1_tarski @ X35)) = (X34))
% 1.72/1.92          | (r2_hidden @ X35 @ X34))),
% 1.72/1.92      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.72/1.92  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.72/1.92  thf('8', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 1.72/1.92      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.72/1.92  thf(t83_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.72/1.92  thf('9', plain,
% 1.72/1.92      (![X22 : $i, X23 : $i]:
% 1.72/1.92         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 1.72/1.92      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.72/1.92  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.72/1.92      inference('sup-', [status(thm)], ['8', '9'])).
% 1.72/1.92  thf(t36_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.72/1.92  thf('11', plain,
% 1.72/1.92      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 1.72/1.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.72/1.92  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.72/1.92      inference('sup+', [status(thm)], ['10', '11'])).
% 1.72/1.92  thf(t106_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.72/1.92       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.72/1.92  thf('13', plain,
% 1.72/1.92      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X8 @ X10)
% 1.72/1.92          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.72/1.92      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.72/1.92  thf('14', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 1.72/1.92      inference('sup-', [status(thm)], ['12', '13'])).
% 1.72/1.92  thf('15', plain,
% 1.72/1.92      (![X2 : $i, X3 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.72/1.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.72/1.92  thf('16', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.72/1.92      inference('sup-', [status(thm)], ['14', '15'])).
% 1.72/1.92  thf('17', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['7', '16'])).
% 1.72/1.92  thf(t70_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i,C:$i]:
% 1.72/1.92     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.72/1.92            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.72/1.92       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.72/1.92            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.72/1.92  thf('18', plain,
% 1.72/1.92      (![X18 : $i, X19 : $i, X21 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X18 @ X19)
% 1.72/1.92          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 1.72/1.92      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.72/1.92  thf('19', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.92         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.72/1.92          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 1.72/1.92      inference('sup-', [status(thm)], ['17', '18'])).
% 1.72/1.92  thf('20', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.72/1.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.72/1.92  thf(t48_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.72/1.92  thf('21', plain,
% 1.72/1.92      (![X15 : $i, X16 : $i]:
% 1.72/1.92         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.72/1.92           = (k3_xboole_0 @ X15 @ X16))),
% 1.72/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.72/1.92  thf('22', plain,
% 1.72/1.92      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 1.72/1.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.72/1.92  thf('23', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('24', plain,
% 1.72/1.92      (![X22 : $i, X23 : $i]:
% 1.72/1.92         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 1.72/1.92      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.72/1.92  thf('25', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 1.72/1.92      inference('sup-', [status(thm)], ['23', '24'])).
% 1.72/1.92  thf('26', plain,
% 1.72/1.92      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X8 @ X10)
% 1.72/1.92          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.72/1.92      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.72/1.92  thf('27', plain,
% 1.72/1.92      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_1) | (r1_xboole_0 @ X0 @ sk_B))),
% 1.72/1.92      inference('sup-', [status(thm)], ['25', '26'])).
% 1.72/1.92  thf('28', plain,
% 1.72/1.92      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 1.72/1.92      inference('sup-', [status(thm)], ['22', '27'])).
% 1.72/1.92  thf('29', plain,
% 1.72/1.92      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 1.72/1.92      inference('sup+', [status(thm)], ['21', '28'])).
% 1.72/1.92  thf('30', plain,
% 1.72/1.92      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_1) @ sk_B)),
% 1.72/1.92      inference('sup+', [status(thm)], ['20', '29'])).
% 1.72/1.92  thf('31', plain,
% 1.72/1.92      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 1.72/1.92      inference('sup+', [status(thm)], ['21', '28'])).
% 1.72/1.92  thf('32', plain,
% 1.72/1.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.72/1.92          | ~ (r1_xboole_0 @ X18 @ X19)
% 1.72/1.92          | ~ (r1_xboole_0 @ X18 @ X20))),
% 1.72/1.92      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.72/1.92  thf('33', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ X1)
% 1.72/1.92          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ 
% 1.72/1.92             (k2_xboole_0 @ sk_B @ X1)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['31', '32'])).
% 1.72/1.92  thf('34', plain,
% 1.72/1.92      ((r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_C_1) @ 
% 1.72/1.92        (k2_xboole_0 @ sk_B @ sk_B))),
% 1.72/1.92      inference('sup-', [status(thm)], ['30', '33'])).
% 1.72/1.92  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.72/1.92      inference('sup-', [status(thm)], ['8', '9'])).
% 1.72/1.92  thf('36', plain,
% 1.72/1.92      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 1.72/1.92      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.72/1.92  thf(t28_xboole_1, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.72/1.92  thf('37', plain,
% 1.72/1.92      (![X11 : $i, X12 : $i]:
% 1.72/1.92         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.72/1.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.72/1.92  thf('38', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.72/1.92           = (k4_xboole_0 @ X0 @ X1))),
% 1.72/1.92      inference('sup-', [status(thm)], ['36', '37'])).
% 1.72/1.92  thf('39', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.72/1.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.72/1.92  thf('40', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.72/1.92           = (k4_xboole_0 @ X0 @ X1))),
% 1.72/1.92      inference('demod', [status(thm)], ['38', '39'])).
% 1.72/1.92  thf('41', plain,
% 1.72/1.92      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.72/1.92      inference('sup+', [status(thm)], ['35', '40'])).
% 1.72/1.92  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.72/1.92      inference('sup-', [status(thm)], ['8', '9'])).
% 1.72/1.92  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.72/1.92      inference('demod', [status(thm)], ['41', '42'])).
% 1.72/1.92  thf('44', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['34', '43'])).
% 1.72/1.92  thf('45', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(t3_xboole_0, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.72/1.92            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.72/1.92       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.72/1.92            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.72/1.92  thf('46', plain,
% 1.72/1.92      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.72/1.92         (~ (r2_hidden @ X6 @ X4)
% 1.72/1.92          | ~ (r2_hidden @ X6 @ X7)
% 1.72/1.92          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.72/1.92      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.72/1.92  thf('47', plain,
% 1.72/1.92      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.72/1.92      inference('sup-', [status(thm)], ['45', '46'])).
% 1.72/1.92  thf('48', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.72/1.92      inference('sup-', [status(thm)], ['44', '47'])).
% 1.72/1.92  thf('49', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 1.72/1.92      inference('sup-', [status(thm)], ['19', '48'])).
% 1.72/1.92  thf('50', plain,
% 1.72/1.92      (![X22 : $i, X23 : $i]:
% 1.72/1.92         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 1.72/1.92      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.72/1.92  thf('51', plain,
% 1.72/1.92      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_tarski @ sk_D))),
% 1.72/1.92      inference('sup-', [status(thm)], ['49', '50'])).
% 1.72/1.92  thf('52', plain,
% 1.72/1.92      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X8 @ X10)
% 1.72/1.92          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.72/1.92      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.72/1.92  thf('53', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 1.72/1.92      inference('sup-', [status(thm)], ['51', '52'])).
% 1.72/1.92  thf('54', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 1.72/1.92      inference('sup-', [status(thm)], ['6', '53'])).
% 1.72/1.92  thf('55', plain,
% 1.72/1.92      (![X2 : $i, X3 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.72/1.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.72/1.92  thf('56', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['54', '55'])).
% 1.72/1.92  thf('57', plain,
% 1.72/1.92      (![X22 : $i, X23 : $i]:
% 1.72/1.92         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 1.72/1.92      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.72/1.92  thf('58', plain,
% 1.72/1.92      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 1.72/1.92      inference('sup-', [status(thm)], ['56', '57'])).
% 1.72/1.92  thf('59', plain,
% 1.72/1.92      (![X15 : $i, X16 : $i]:
% 1.72/1.92         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.72/1.92           = (k3_xboole_0 @ X15 @ X16))),
% 1.72/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.72/1.92  thf('60', plain,
% 1.72/1.92      (![X15 : $i, X16 : $i]:
% 1.72/1.92         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.72/1.92           = (k3_xboole_0 @ X15 @ X16))),
% 1.72/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.72/1.92  thf('61', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.72/1.92           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['59', '60'])).
% 1.72/1.92  thf('62', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.72/1.92           = (k4_xboole_0 @ X0 @ X1))),
% 1.72/1.92      inference('demod', [status(thm)], ['38', '39'])).
% 1.72/1.92  thf('63', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]:
% 1.72/1.92         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.72/1.92           = (k4_xboole_0 @ X1 @ X0))),
% 1.72/1.92      inference('demod', [status(thm)], ['61', '62'])).
% 1.72/1.92  thf('64', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['58', '63'])).
% 1.72/1.92  thf('65', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 1.72/1.92      inference('sup-', [status(thm)], ['12', '13'])).
% 1.72/1.92  thf('66', plain,
% 1.72/1.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.72/1.92          | ~ (r1_xboole_0 @ X18 @ X19)
% 1.72/1.92          | ~ (r1_xboole_0 @ X18 @ X20))),
% 1.72/1.92      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.72/1.92  thf('67', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.92         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.72/1.92          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['65', '66'])).
% 1.72/1.92  thf('68', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.72/1.92          | (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 1.72/1.92             (k2_xboole_0 @ sk_A @ X0)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['64', '67'])).
% 1.72/1.92  thf('69', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['58', '63'])).
% 1.72/1.92  thf('70', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.72/1.92          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.72/1.92      inference('demod', [status(thm)], ['68', '69'])).
% 1.72/1.92  thf('71', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 1.72/1.92      inference('sup-', [status(thm)], ['3', '70'])).
% 1.72/1.92  thf('72', plain,
% 1.72/1.92      (![X2 : $i, X3 : $i]:
% 1.72/1.92         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.72/1.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.72/1.92  thf('73', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.72/1.92      inference('sup-', [status(thm)], ['71', '72'])).
% 1.72/1.92  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 1.72/1.92  
% 1.72/1.92  % SZS output end Refutation
% 1.72/1.92  
% 1.72/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
