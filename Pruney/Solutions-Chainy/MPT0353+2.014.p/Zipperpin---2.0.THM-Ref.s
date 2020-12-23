%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oBzvN06XQ0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:15 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 267 expanded)
%              Number of leaves         :   22 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  780 (2611 expanded)
%              Number of equality atoms :   74 ( 215 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['14','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('34',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('46',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('48',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('57',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['36','64'])).

thf('66',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('68',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('74',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X22 @ X20 @ X21 )
        = ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oBzvN06XQ0
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:24:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.06/1.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.26  % Solved by: fo/fo7.sh
% 1.06/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.26  % done 535 iterations in 0.788s
% 1.06/1.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.26  % SZS output start Refutation
% 1.06/1.26  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.06/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.26  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.26  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.06/1.26  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.06/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.26  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.06/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.26  thf(t32_subset_1, conjecture,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26       ( ![C:$i]:
% 1.06/1.26         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26           ( ( k7_subset_1 @ A @ B @ C ) =
% 1.06/1.26             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.06/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.26    (~( ![A:$i,B:$i]:
% 1.06/1.26        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26          ( ![C:$i]:
% 1.06/1.26            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26              ( ( k7_subset_1 @ A @ B @ C ) =
% 1.06/1.26                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 1.06/1.26    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 1.06/1.26  thf('0', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(involutiveness_k3_subset_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.06/1.26  thf('1', plain,
% 1.06/1.26      (![X15 : $i, X16 : $i]:
% 1.06/1.26         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 1.06/1.26          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.06/1.26      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.26  thf('2', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 1.06/1.26      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.26  thf('3', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(d5_subset_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.06/1.26  thf('4', plain,
% 1.06/1.26      (![X11 : $i, X12 : $i]:
% 1.06/1.26         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 1.06/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.06/1.26      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.26  thf('5', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.06/1.26      inference('sup-', [status(thm)], ['3', '4'])).
% 1.06/1.26  thf('6', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 1.06/1.26      inference('demod', [status(thm)], ['2', '5'])).
% 1.06/1.26  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(dt_k3_subset_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.06/1.26  thf('8', plain,
% 1.06/1.26      (![X13 : $i, X14 : $i]:
% 1.06/1.26         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 1.06/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 1.06/1.26      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.06/1.26  thf('9', plain,
% 1.06/1.26      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.26  thf('10', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.06/1.26      inference('sup-', [status(thm)], ['3', '4'])).
% 1.06/1.26  thf('11', plain,
% 1.06/1.26      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.26  thf('12', plain,
% 1.06/1.26      (![X11 : $i, X12 : $i]:
% 1.06/1.26         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 1.06/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.06/1.26      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.26  thf('13', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 1.06/1.26         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['11', '12'])).
% 1.06/1.26  thf('14', plain,
% 1.06/1.26      (((sk_C) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['6', '13'])).
% 1.06/1.26  thf(idempotence_k3_xboole_0, axiom,
% 1.06/1.26    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.06/1.26  thf('15', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.06/1.26      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.06/1.26  thf(t112_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.06/1.26       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.06/1.26  thf('16', plain,
% 1.06/1.26      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ (k3_xboole_0 @ X5 @ X7) @ (k3_xboole_0 @ X6 @ X7))
% 1.06/1.26           = (k3_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7))),
% 1.06/1.26      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.06/1.26  thf('17', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.06/1.26           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['15', '16'])).
% 1.06/1.26  thf(commutativity_k3_xboole_0, axiom,
% 1.06/1.26    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.06/1.26  thf('18', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.26  thf('19', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.06/1.26           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.06/1.26      inference('demod', [status(thm)], ['17', '18'])).
% 1.06/1.26  thf('20', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.26  thf(t100_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.06/1.26  thf('21', plain,
% 1.06/1.26      (![X3 : $i, X4 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X3 @ X4)
% 1.06/1.26           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.26  thf('22', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.26           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['20', '21'])).
% 1.06/1.26  thf('23', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X1 @ X0)
% 1.06/1.26           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['19', '22'])).
% 1.06/1.26  thf('24', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.06/1.26      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.06/1.26  thf(t16_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.06/1.26       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.06/1.26  thf('25', plain,
% 1.06/1.26      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.26         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 1.06/1.26           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.06/1.26  thf('26', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k3_xboole_0 @ X0 @ X1)
% 1.06/1.26           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['24', '25'])).
% 1.06/1.26  thf('27', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 1.06/1.26           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['23', '26'])).
% 1.06/1.26  thf('28', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X1 @ X0)
% 1.06/1.26           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['19', '22'])).
% 1.06/1.26  thf('29', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X1 @ X0)
% 1.06/1.26           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['27', '28'])).
% 1.06/1.26  thf('30', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 1.06/1.26         = (k3_xboole_0 @ sk_A @ sk_C))),
% 1.06/1.26      inference('sup+', [status(thm)], ['14', '29'])).
% 1.06/1.26  thf('31', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.26  thf('32', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 1.06/1.26         = (k3_xboole_0 @ sk_C @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['30', '31'])).
% 1.06/1.26  thf('33', plain,
% 1.06/1.26      (((sk_C) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['6', '13'])).
% 1.06/1.26  thf('34', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))),
% 1.06/1.26      inference('sup+', [status(thm)], ['32', '33'])).
% 1.06/1.26  thf('35', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.26           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['20', '21'])).
% 1.06/1.26  thf('36', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 1.06/1.26      inference('sup+', [status(thm)], ['34', '35'])).
% 1.06/1.26  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('38', plain,
% 1.06/1.26      (![X15 : $i, X16 : $i]:
% 1.06/1.26         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 1.06/1.26          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.06/1.26      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.26  thf('39', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.26      inference('sup-', [status(thm)], ['37', '38'])).
% 1.06/1.26  thf('40', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('41', plain,
% 1.06/1.26      (![X11 : $i, X12 : $i]:
% 1.06/1.26         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 1.06/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.06/1.26      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.26  thf('42', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.06/1.26      inference('sup-', [status(thm)], ['40', '41'])).
% 1.06/1.26  thf('43', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.26      inference('demod', [status(thm)], ['39', '42'])).
% 1.06/1.26  thf('44', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('45', plain,
% 1.06/1.26      (![X13 : $i, X14 : $i]:
% 1.06/1.26         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 1.06/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 1.06/1.26      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.06/1.26  thf('46', plain,
% 1.06/1.26      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['44', '45'])).
% 1.06/1.26  thf('47', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.06/1.26      inference('sup-', [status(thm)], ['40', '41'])).
% 1.06/1.26  thf('48', plain,
% 1.06/1.26      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['46', '47'])).
% 1.06/1.26  thf('49', plain,
% 1.06/1.26      (![X11 : $i, X12 : $i]:
% 1.06/1.26         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 1.06/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.06/1.26      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.26  thf('50', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 1.06/1.26         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['48', '49'])).
% 1.06/1.26  thf('51', plain,
% 1.06/1.26      (((sk_B) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['43', '50'])).
% 1.06/1.26  thf('52', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X1 @ X0)
% 1.06/1.26           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['27', '28'])).
% 1.06/1.26  thf('53', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 1.06/1.26         = (k3_xboole_0 @ sk_A @ sk_B))),
% 1.06/1.26      inference('sup+', [status(thm)], ['51', '52'])).
% 1.06/1.26  thf('54', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.26  thf('55', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 1.06/1.26         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['53', '54'])).
% 1.06/1.26  thf('56', plain,
% 1.06/1.26      (((sk_B) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['43', '50'])).
% 1.06/1.26  thf('57', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.06/1.26      inference('sup+', [status(thm)], ['55', '56'])).
% 1.06/1.26  thf('58', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.26  thf('59', plain,
% 1.06/1.26      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ (k3_xboole_0 @ X5 @ X7) @ (k3_xboole_0 @ X6 @ X7))
% 1.06/1.26           = (k3_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7))),
% 1.06/1.26      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.06/1.26  thf('60', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 1.06/1.26           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['58', '59'])).
% 1.06/1.26  thf('61', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 1.06/1.26           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.06/1.26      inference('sup+', [status(thm)], ['57', '60'])).
% 1.06/1.26  thf('62', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.26           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['20', '21'])).
% 1.06/1.26  thf('63', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.26  thf('64', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ sk_B @ X0)
% 1.06/1.26           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.06/1.26  thf('65', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_B @ sk_C)
% 1.06/1.26         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['36', '64'])).
% 1.06/1.26  thf('66', plain,
% 1.06/1.26      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 1.06/1.26         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('67', plain,
% 1.06/1.26      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.06/1.26      inference('sup-', [status(thm)], ['3', '4'])).
% 1.06/1.26  thf('68', plain,
% 1.06/1.26      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 1.06/1.26         != (k9_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.06/1.26      inference('demod', [status(thm)], ['66', '67'])).
% 1.06/1.26  thf('69', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(redefinition_k7_subset_1, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.06/1.26  thf('70', plain,
% 1.06/1.26      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.26         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 1.06/1.26          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 1.06/1.26      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.06/1.26  thf('71', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['69', '70'])).
% 1.06/1.26  thf('72', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_B @ sk_C)
% 1.06/1.26         != (k9_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.06/1.26      inference('demod', [status(thm)], ['68', '71'])).
% 1.06/1.26  thf('73', plain,
% 1.06/1.26      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.26  thf(redefinition_k9_subset_1, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.06/1.26  thf('74', plain,
% 1.06/1.26      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.26         (((k9_subset_1 @ X22 @ X20 @ X21) = (k3_xboole_0 @ X20 @ X21))
% 1.06/1.26          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 1.06/1.26      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.06/1.26  thf('75', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         ((k9_subset_1 @ sk_A @ X0 @ (k4_xboole_0 @ sk_A @ sk_C))
% 1.06/1.26           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['73', '74'])).
% 1.06/1.26  thf('76', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_B @ sk_C)
% 1.06/1.26         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.06/1.26      inference('demod', [status(thm)], ['72', '75'])).
% 1.06/1.26  thf('77', plain, ($false),
% 1.06/1.26      inference('simplify_reflect-', [status(thm)], ['65', '76'])).
% 1.06/1.26  
% 1.06/1.26  % SZS output end Refutation
% 1.06/1.26  
% 1.06/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
