%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Vr1P03Ab6

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:16 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 217 expanded)
%              Number of leaves         :   24 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  716 (1793 expanded)
%              Number of equality atoms :   73 ( 180 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k6_subset_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k6_subset_1 @ X18 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ( k6_subset_1 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k9_subset_1 @ X23 @ X21 @ X22 )
        = ( k3_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k6_subset_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ ( k6_subset_1 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k9_subset_1 @ X23 @ X21 @ X22 )
        = ( k3_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ ( k6_subset_1 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['20','38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X15 @ ( k3_subset_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','37'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('62',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( k6_subset_1 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k6_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['47','67'])).

thf('69',plain,(
    ( k6_subset_1 @ sk_B @ sk_C )
 != ( k6_subset_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['12','15','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Vr1P03Ab6
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 448 iterations in 0.205s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(t32_subset_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66       ( ![C:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.46/0.66             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i]:
% 0.46/0.66        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66          ( ![C:$i]:
% 0.46/0.66            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66              ( ( k7_subset_1 @ A @ B @ C ) =
% 0.46/0.66                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 0.46/0.66         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d5_subset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.66  thf(redefinition_k6_subset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         (((k3_subset_1 @ X10 @ X11) = (k6_subset_1 @ X10 @ X11))
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '4'])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 0.46/0.66         != (k9_subset_1 @ sk_A @ sk_B @ (k6_subset_1 @ sk_A @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '5'])).
% 0.46/0.66  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(redefinition_k7_subset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.46/0.66          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.46/0.66          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k6_subset_1 @ X18 @ X20)))),
% 0.46/0.66      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k6_subset_1 @ sk_B @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['7', '10'])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (((k6_subset_1 @ sk_B @ sk_C)
% 0.46/0.66         != (k9_subset_1 @ sk_A @ sk_B @ (k6_subset_1 @ sk_A @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '11'])).
% 0.46/0.66  thf(dt_k6_subset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i]:
% 0.46/0.66         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.46/0.66  thf(redefinition_k9_subset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.66         (((k9_subset_1 @ X23 @ X21 @ X22) = (k3_xboole_0 @ X21 @ X22))
% 0.46/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k9_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 0.46/0.66           = (k3_xboole_0 @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('16', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(involutiveness_k3_subset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.46/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '4'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (((k3_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i]:
% 0.46/0.66         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         (((k3_subset_1 @ X10 @ X11) = (k6_subset_1 @ X10 @ X11))
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.46/0.66           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf(t48_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.46/0.66           = (k3_xboole_0 @ X8 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X8 @ (k6_subset_1 @ X8 @ X9))
% 0.46/0.66           = (k3_xboole_0 @ X8 @ X9))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.46/0.66  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.66  thf('28', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X0 : $i]: ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X0)) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X12 : $i, X13 : $i]:
% 0.46/0.66         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.46/0.66  thf('31', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['29', '30'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.66         (((k9_subset_1 @ X23 @ X21 @ X22) = (k3_xboole_0 @ X21 @ X22))
% 0.46/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X0 @ X1) = (k9_subset_1 @ X0 @ X1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X8 @ (k6_subset_1 @ X8 @ X9))
% 0.46/0.66           = (k3_xboole_0 @ X8 @ X9))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.46/0.66           = (k9_subset_1 @ X0 @ X1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.46/0.66           = (k9_subset_1 @ X0 @ X1 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['23', '37'])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X0 @ X1) = (k9_subset_1 @ X0 @ X1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('41', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '38', '39', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf(t100_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X3 @ X4)
% 0.46/0.66           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X3 @ X4)
% 0.46/0.66           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.46/0.66      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['42', '45'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (((k6_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['41', '46'])).
% 0.46/0.66  thf('48', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (((k3_subset_1 @ X15 @ (k3_subset_1 @ X15 @ X14)) = (X14))
% 0.46/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.66  thf('51', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (((k3_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['50', '55'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.46/0.66           = (k9_subset_1 @ X0 @ X1 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['23', '37'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X0 @ X1) = (k9_subset_1 @ X0 @ X1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('60', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf(t112_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.46/0.66       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k3_xboole_0 @ X5 @ X7) @ (k3_xboole_0 @ X6 @ X7))
% 0.46/0.66           = (k3_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.46/0.66           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['61', '62'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.46/0.66           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['60', '63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k6_subset_1 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['42', '45'])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k6_subset_1 @ sk_B @ X0)
% 0.46/0.66           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (((k6_subset_1 @ sk_B @ sk_C)
% 0.46/0.66         = (k3_xboole_0 @ sk_B @ (k6_subset_1 @ sk_A @ sk_C)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['47', '67'])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (((k6_subset_1 @ sk_B @ sk_C) != (k6_subset_1 @ sk_B @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['12', '15', '68'])).
% 0.46/0.66  thf('70', plain, ($false), inference('simplify', [status(thm)], ['69'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
