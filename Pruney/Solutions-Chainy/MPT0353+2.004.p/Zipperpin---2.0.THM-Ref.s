%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xpagmu8BE3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:14 EST 2020

% Result     : Theorem 3.02s
% Output     : Refutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 349 expanded)
%              Number of leaves         :   23 ( 119 expanded)
%              Depth                    :   15
%              Number of atoms          :  968 (3480 expanded)
%              Number of equality atoms :   91 ( 295 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X11 @ X13 @ X12 )
        = ( k9_subset_1 @ X11 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_B )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k9_subset_1 @ X26 @ X24 @ X25 )
        = ( k3_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','15','16'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_B )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_A @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_A @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','54'])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['35','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('64',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['66','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['58','65'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('84',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82','89'])).

thf('91',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['17','90'])).

thf('92',plain,(
    $false ),
    inference(simplify,[status(thm)],['91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xpagmu8BE3
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:52:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 3.02/3.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.02/3.23  % Solved by: fo/fo7.sh
% 3.02/3.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.02/3.23  % done 787 iterations in 2.754s
% 3.02/3.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.02/3.23  % SZS output start Refutation
% 3.02/3.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.02/3.23  thf(sk_B_type, type, sk_B: $i).
% 3.02/3.23  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.02/3.23  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 3.02/3.23  thf(sk_C_type, type, sk_C: $i).
% 3.02/3.23  thf(sk_A_type, type, sk_A: $i).
% 3.02/3.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.02/3.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.02/3.23  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.02/3.23  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.02/3.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.02/3.23  thf(t32_subset_1, conjecture,
% 3.02/3.23    (![A:$i,B:$i]:
% 3.02/3.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23       ( ![C:$i]:
% 3.02/3.23         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23           ( ( k7_subset_1 @ A @ B @ C ) =
% 3.02/3.23             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 3.02/3.23  thf(zf_stmt_0, negated_conjecture,
% 3.02/3.23    (~( ![A:$i,B:$i]:
% 3.02/3.23        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23          ( ![C:$i]:
% 3.02/3.23            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23              ( ( k7_subset_1 @ A @ B @ C ) =
% 3.02/3.23                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 3.02/3.23    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 3.02/3.23  thf('0', plain,
% 3.02/3.23      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 3.02/3.23         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 3.02/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.23  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.23  thf(d5_subset_1, axiom,
% 3.02/3.23    (![A:$i,B:$i]:
% 3.02/3.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.02/3.23  thf('2', plain,
% 3.02/3.23      (![X14 : $i, X15 : $i]:
% 3.02/3.23         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 3.02/3.23          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 3.02/3.23      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.02/3.23  thf('3', plain,
% 3.02/3.23      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 3.02/3.23      inference('sup-', [status(thm)], ['1', '2'])).
% 3.02/3.23  thf('4', plain,
% 3.02/3.23      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 3.02/3.23         != (k9_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 3.02/3.23      inference('demod', [status(thm)], ['0', '3'])).
% 3.02/3.23  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.23  thf(redefinition_k7_subset_1, axiom,
% 3.02/3.23    (![A:$i,B:$i,C:$i]:
% 3.02/3.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.02/3.23  thf('6', plain,
% 3.02/3.23      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.02/3.23         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 3.02/3.23          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 3.02/3.23      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.02/3.23  thf('7', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 3.02/3.23      inference('sup-', [status(thm)], ['5', '6'])).
% 3.02/3.23  thf('8', plain,
% 3.02/3.23      (((k4_xboole_0 @ sk_B @ sk_C)
% 3.02/3.23         != (k9_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 3.02/3.23      inference('demod', [status(thm)], ['4', '7'])).
% 3.02/3.23  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.23  thf(commutativity_k9_subset_1, axiom,
% 3.02/3.23    (![A:$i,B:$i,C:$i]:
% 3.02/3.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 3.02/3.23  thf('10', plain,
% 3.02/3.23      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.02/3.23         (((k9_subset_1 @ X11 @ X13 @ X12) = (k9_subset_1 @ X11 @ X12 @ X13))
% 3.02/3.23          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 3.02/3.23  thf('11', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k9_subset_1 @ sk_A @ X0 @ sk_B) = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 3.02/3.23      inference('sup-', [status(thm)], ['9', '10'])).
% 3.02/3.23  thf('12', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.23  thf(redefinition_k9_subset_1, axiom,
% 3.02/3.23    (![A:$i,B:$i,C:$i]:
% 3.02/3.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 3.02/3.23  thf('13', plain,
% 3.02/3.23      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.02/3.23         (((k9_subset_1 @ X26 @ X24 @ X25) = (k3_xboole_0 @ X24 @ X25))
% 3.02/3.23          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 3.02/3.23      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 3.02/3.23  thf('14', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k9_subset_1 @ sk_A @ X0 @ sk_B) = (k3_xboole_0 @ X0 @ sk_B))),
% 3.02/3.23      inference('sup-', [status(thm)], ['12', '13'])).
% 3.02/3.23  thf('15', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X0 @ sk_B) = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 3.02/3.23      inference('demod', [status(thm)], ['11', '14'])).
% 3.02/3.23  thf(commutativity_k3_xboole_0, axiom,
% 3.02/3.23    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.02/3.23  thf('16', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('17', plain,
% 3.02/3.23      (((k4_xboole_0 @ sk_B @ sk_C)
% 3.02/3.23         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 3.02/3.23      inference('demod', [status(thm)], ['8', '15', '16'])).
% 3.02/3.23  thf(idempotence_k3_xboole_0, axiom,
% 3.02/3.23    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 3.02/3.23  thf('18', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 3.02/3.23      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.02/3.23  thf('19', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf(t16_xboole_1, axiom,
% 3.02/3.23    (![A:$i,B:$i,C:$i]:
% 3.02/3.23     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 3.02/3.23       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 3.02/3.23  thf('20', plain,
% 3.02/3.23      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 3.02/3.23           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 3.02/3.23      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.02/3.23  thf('21', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.02/3.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['19', '20'])).
% 3.02/3.23  thf('22', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X1 @ X0)
% 3.02/3.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.02/3.23      inference('sup+', [status(thm)], ['18', '21'])).
% 3.02/3.23  thf('23', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 3.02/3.23      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.02/3.23  thf('24', plain,
% 3.02/3.23      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 3.02/3.23           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 3.02/3.23      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.02/3.23  thf('25', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X0 @ X1)
% 3.02/3.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['23', '24'])).
% 3.02/3.23  thf('26', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X1 @ X0)
% 3.02/3.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('demod', [status(thm)], ['22', '25'])).
% 3.02/3.23  thf('27', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X0 @ X1)
% 3.02/3.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['23', '24'])).
% 3.02/3.23  thf(t100_xboole_1, axiom,
% 3.02/3.23    (![A:$i,B:$i]:
% 3.02/3.23     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.02/3.23  thf('28', plain,
% 3.02/3.23      (![X3 : $i, X4 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ X3 @ X4)
% 3.02/3.23           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.02/3.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.02/3.23  thf('29', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.02/3.23           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['27', '28'])).
% 3.02/3.23  thf('30', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 3.02/3.23           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['26', '29'])).
% 3.02/3.23  thf('31', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X1 @ X0)
% 3.02/3.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('demod', [status(thm)], ['22', '25'])).
% 3.02/3.23  thf('32', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('33', plain,
% 3.02/3.23      (![X3 : $i, X4 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ X3 @ X4)
% 3.02/3.23           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.02/3.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.02/3.23  thf('34', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ X0 @ X1)
% 3.02/3.23           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['32', '33'])).
% 3.02/3.23  thf('35', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.02/3.23           = (k4_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('demod', [status(thm)], ['30', '31', '34'])).
% 3.02/3.23  thf('36', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k9_subset_1 @ sk_A @ X0 @ sk_B) = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 3.02/3.23      inference('sup-', [status(thm)], ['9', '10'])).
% 3.02/3.23  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.23  thf(dt_k9_subset_1, axiom,
% 3.02/3.23    (![A:$i,B:$i,C:$i]:
% 3.02/3.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.02/3.23  thf('38', plain,
% 3.02/3.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.02/3.23         ((m1_subset_1 @ (k9_subset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X16))
% 3.02/3.23          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X16)))),
% 3.02/3.23      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 3.02/3.23  thf('39', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         (m1_subset_1 @ (k9_subset_1 @ sk_A @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('sup-', [status(thm)], ['37', '38'])).
% 3.02/3.23  thf('40', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         (m1_subset_1 @ (k9_subset_1 @ sk_A @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('sup+', [status(thm)], ['36', '39'])).
% 3.02/3.23  thf(involutiveness_k3_subset_1, axiom,
% 3.02/3.23    (![A:$i,B:$i]:
% 3.02/3.23     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.23       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 3.02/3.23  thf('41', plain,
% 3.02/3.23      (![X19 : $i, X20 : $i]:
% 3.02/3.23         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 3.02/3.23          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 3.02/3.23      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.02/3.23  thf('42', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k3_subset_1 @ sk_A @ 
% 3.02/3.23           (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ X0)))
% 3.02/3.23           = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 3.02/3.23      inference('sup-', [status(thm)], ['40', '41'])).
% 3.02/3.23  thf('43', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X0 @ sk_B) = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 3.02/3.23      inference('demod', [status(thm)], ['11', '14'])).
% 3.02/3.23  thf('44', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X0 @ sk_B) = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 3.02/3.23      inference('demod', [status(thm)], ['11', '14'])).
% 3.02/3.23  thf('45', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k3_subset_1 @ sk_A @ 
% 3.02/3.23           (k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))
% 3.02/3.23           = (k3_xboole_0 @ X0 @ sk_B))),
% 3.02/3.23      inference('demod', [status(thm)], ['42', '43', '44'])).
% 3.02/3.23  thf('46', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('47', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('48', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         (m1_subset_1 @ (k9_subset_1 @ sk_A @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('sup-', [status(thm)], ['37', '38'])).
% 3.02/3.23  thf('49', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k9_subset_1 @ sk_A @ X0 @ sk_B) = (k3_xboole_0 @ X0 @ sk_B))),
% 3.02/3.23      inference('sup-', [status(thm)], ['12', '13'])).
% 3.02/3.23  thf('50', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('demod', [status(thm)], ['48', '49'])).
% 3.02/3.23  thf('51', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('sup+', [status(thm)], ['47', '50'])).
% 3.02/3.23  thf('52', plain,
% 3.02/3.23      (![X14 : $i, X15 : $i]:
% 3.02/3.23         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 3.02/3.23          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 3.02/3.23      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.02/3.23  thf('53', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 3.02/3.23           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 3.02/3.23      inference('sup-', [status(thm)], ['51', '52'])).
% 3.02/3.23  thf('54', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 3.02/3.23           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['46', '53'])).
% 3.02/3.23  thf('55', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k3_subset_1 @ sk_A @ 
% 3.02/3.23           (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))
% 3.02/3.23           = (k3_xboole_0 @ X0 @ sk_B))),
% 3.02/3.23      inference('demod', [status(thm)], ['45', '54'])).
% 3.02/3.23  thf('56', plain,
% 3.02/3.23      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 3.02/3.23         = (k3_xboole_0 @ sk_A @ sk_B))),
% 3.02/3.23      inference('sup+', [status(thm)], ['35', '55'])).
% 3.02/3.23  thf('57', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('58', plain,
% 3.02/3.23      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 3.02/3.23         = (k3_xboole_0 @ sk_B @ sk_A))),
% 3.02/3.23      inference('demod', [status(thm)], ['56', '57'])).
% 3.02/3.23  thf('59', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.23  thf('60', plain,
% 3.02/3.23      (![X19 : $i, X20 : $i]:
% 3.02/3.23         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 3.02/3.23          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 3.02/3.23      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.02/3.23  thf('61', plain,
% 3.02/3.23      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 3.02/3.23      inference('sup-', [status(thm)], ['59', '60'])).
% 3.02/3.23  thf('62', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.02/3.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.23  thf('63', plain,
% 3.02/3.23      (![X14 : $i, X15 : $i]:
% 3.02/3.23         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 3.02/3.23          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 3.02/3.23      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.02/3.23  thf('64', plain,
% 3.02/3.23      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.02/3.23      inference('sup-', [status(thm)], ['62', '63'])).
% 3.02/3.23  thf('65', plain,
% 3.02/3.23      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 3.02/3.23      inference('demod', [status(thm)], ['61', '64'])).
% 3.02/3.23  thf('66', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 3.02/3.23      inference('sup+', [status(thm)], ['58', '65'])).
% 3.02/3.23  thf('67', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('68', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X0 @ X1)
% 3.02/3.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['23', '24'])).
% 3.02/3.23  thf('69', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X0 @ X1)
% 3.02/3.23           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['67', '68'])).
% 3.02/3.23  thf(t112_xboole_1, axiom,
% 3.02/3.23    (![A:$i,B:$i,C:$i]:
% 3.02/3.23     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 3.02/3.23       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 3.02/3.23  thf('70', plain,
% 3.02/3.23      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.02/3.23         ((k5_xboole_0 @ (k3_xboole_0 @ X5 @ X7) @ (k3_xboole_0 @ X6 @ X7))
% 3.02/3.23           = (k3_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7))),
% 3.02/3.23      inference('cnf', [status(esa)], [t112_xboole_1])).
% 3.02/3.23  thf('71', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.23         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 3.02/3.23           (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 3.02/3.23           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X0 @ X1)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['69', '70'])).
% 3.02/3.23  thf('72', plain,
% 3.02/3.23      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 3.02/3.23           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 3.02/3.23      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.02/3.23  thf('73', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('74', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 3.02/3.23           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['72', '73'])).
% 3.02/3.23  thf('75', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.23         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 3.02/3.23           (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 3.02/3.23           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X2) @ X0)))),
% 3.02/3.23      inference('demod', [status(thm)], ['71', '74'])).
% 3.02/3.23  thf('76', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 3.02/3.23           (k3_xboole_0 @ X0 @ sk_B))
% 3.02/3.23           = (k3_xboole_0 @ sk_A @ 
% 3.02/3.23              (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['66', '75'])).
% 3.02/3.23  thf('77', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('78', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 3.02/3.23      inference('sup+', [status(thm)], ['58', '65'])).
% 3.02/3.23  thf('79', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ X0 @ X1)
% 3.02/3.23           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['32', '33'])).
% 3.02/3.23  thf('80', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('81', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.23         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 3.02/3.23           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['72', '73'])).
% 3.02/3.23  thf('82', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('83', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 3.02/3.23      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.02/3.23  thf('84', plain,
% 3.02/3.23      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.02/3.23         ((k5_xboole_0 @ (k3_xboole_0 @ X5 @ X7) @ (k3_xboole_0 @ X6 @ X7))
% 3.02/3.23           = (k3_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7))),
% 3.02/3.23      inference('cnf', [status(esa)], [t112_xboole_1])).
% 3.02/3.23  thf('85', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.02/3.23           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 3.02/3.23      inference('sup+', [status(thm)], ['83', '84'])).
% 3.02/3.23  thf('86', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.02/3.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.02/3.23  thf('87', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.02/3.23           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 3.02/3.23      inference('demod', [status(thm)], ['85', '86'])).
% 3.02/3.23  thf('88', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ X0 @ X1)
% 3.02/3.23           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['32', '33'])).
% 3.02/3.23  thf('89', plain,
% 3.02/3.23      (![X0 : $i, X1 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ X1 @ X0)
% 3.02/3.23           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.02/3.23      inference('sup+', [status(thm)], ['87', '88'])).
% 3.02/3.23  thf('90', plain,
% 3.02/3.23      (![X0 : $i]:
% 3.02/3.23         ((k4_xboole_0 @ sk_B @ X0)
% 3.02/3.23           = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)))),
% 3.02/3.23      inference('demod', [status(thm)],
% 3.02/3.23                ['76', '77', '78', '79', '80', '81', '82', '89'])).
% 3.02/3.23  thf('91', plain,
% 3.02/3.23      (((k4_xboole_0 @ sk_B @ sk_C) != (k4_xboole_0 @ sk_B @ sk_C))),
% 3.02/3.23      inference('demod', [status(thm)], ['17', '90'])).
% 3.02/3.23  thf('92', plain, ($false), inference('simplify', [status(thm)], ['91'])).
% 3.02/3.23  
% 3.02/3.23  % SZS output end Refutation
% 3.02/3.23  
% 3.02/3.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
