%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3hBl8wjZ9U

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:07 EST 2020

% Result     : Theorem 3.19s
% Output     : Refutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  141 (1534 expanded)
%              Number of leaves         :   23 ( 470 expanded)
%              Depth                    :   28
%              Number of atoms          : 1123 (17457 expanded)
%              Number of equality atoms :  107 (1286 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t46_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( ( r1_xboole_0 @ B @ C )
              & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
           => ( B
              = ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( ( r1_xboole_0 @ B @ C )
                & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
             => ( B
                = ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(simplify,[status(thm)],['18'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('21',plain,
    ( sk_C
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('28',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X44 @ ( k3_subset_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['21','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('38',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X44 @ ( k3_subset_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('55',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('61',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','11'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','11'])).

thf('68',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','11'])).

thf('72',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','11'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['70','82'])).

thf('84',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('85',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('91',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['69','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['68','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('113',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( sk_B
    = ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['35','58','113'])).

thf('115',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3hBl8wjZ9U
% 0.13/0.36  % Computer   : n016.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 14:37:04 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 3.19/3.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.19/3.43  % Solved by: fo/fo7.sh
% 3.19/3.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.19/3.43  % done 3080 iterations in 2.948s
% 3.19/3.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.19/3.43  % SZS output start Refutation
% 3.19/3.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.19/3.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.19/3.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.19/3.43  thf(sk_C_type, type, sk_C: $i).
% 3.19/3.43  thf(sk_B_type, type, sk_B: $i).
% 3.19/3.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.19/3.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.19/3.43  thf(sk_A_type, type, sk_A: $i).
% 3.19/3.43  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.19/3.43  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.19/3.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.19/3.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.19/3.43  thf(t46_subset_1, conjecture,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.19/3.43       ( ![C:$i]:
% 3.19/3.43         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.19/3.43           ( ( ( r1_xboole_0 @ B @ C ) & 
% 3.19/3.43               ( r1_xboole_0 @
% 3.19/3.43                 ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 3.19/3.43             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 3.19/3.43  thf(zf_stmt_0, negated_conjecture,
% 3.19/3.43    (~( ![A:$i,B:$i]:
% 3.19/3.43        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.19/3.43          ( ![C:$i]:
% 3.19/3.43            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.19/3.43              ( ( ( r1_xboole_0 @ B @ C ) & 
% 3.19/3.43                  ( r1_xboole_0 @
% 3.19/3.43                    ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 3.19/3.43                ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 3.19/3.43    inference('cnf.neg', [status(esa)], [t46_subset_1])).
% 3.19/3.43  thf('0', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(d5_subset_1, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.19/3.43       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.19/3.43  thf('1', plain,
% 3.19/3.43      (![X39 : $i, X40 : $i]:
% 3.19/3.43         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 3.19/3.43          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 3.19/3.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.19/3.43  thf('2', plain,
% 3.19/3.43      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['0', '1'])).
% 3.19/3.43  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('4', plain,
% 3.19/3.43      (![X39 : $i, X40 : $i]:
% 3.19/3.43         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 3.19/3.43          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 3.19/3.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.19/3.43  thf('5', plain,
% 3.19/3.43      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.19/3.43      inference('sup-', [status(thm)], ['3', '4'])).
% 3.19/3.43  thf(t53_xboole_1, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 3.19/3.43       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 3.19/3.43  thf('6', plain,
% 3.19/3.43      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 3.19/3.43           = (k3_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ 
% 3.19/3.43              (k4_xboole_0 @ X15 @ X17)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t53_xboole_1])).
% 3.19/3.43  thf('7', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 3.19/3.43           = (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 3.19/3.43              (k4_xboole_0 @ sk_A @ X0)))),
% 3.19/3.43      inference('sup+', [status(thm)], ['5', '6'])).
% 3.19/3.43  thf('8', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 3.19/3.43         = (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 3.19/3.43            (k3_subset_1 @ sk_A @ sk_C)))),
% 3.19/3.43      inference('sup+', [status(thm)], ['2', '7'])).
% 3.19/3.43  thf('9', plain,
% 3.19/3.43      ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ (k3_subset_1 @ sk_A @ sk_C))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(d7_xboole_0, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.19/3.43       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.19/3.43  thf('10', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 3.19/3.43      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.19/3.43  thf('11', plain,
% 3.19/3.43      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 3.19/3.43         (k3_subset_1 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['9', '10'])).
% 3.19/3.43  thf('12', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['8', '11'])).
% 3.19/3.43  thf(t41_xboole_1, axiom,
% 3.19/3.43    (![A:$i,B:$i,C:$i]:
% 3.19/3.43     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.19/3.43       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.19/3.43  thf('13', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.19/3.43           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.19/3.43  thf(t37_xboole_1, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.19/3.43  thf('14', plain,
% 3.19/3.43      (![X7 : $i, X8 : $i]:
% 3.19/3.43         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t37_xboole_1])).
% 3.19/3.43  thf('15', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.43         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.19/3.43          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['13', '14'])).
% 3.19/3.43  thf('16', plain,
% 3.19/3.43      ((((k1_xboole_0) != (k1_xboole_0))
% 3.19/3.43        | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['12', '15'])).
% 3.19/3.43  thf('17', plain,
% 3.19/3.43      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.19/3.43      inference('sup-', [status(thm)], ['3', '4'])).
% 3.19/3.43  thf('18', plain,
% 3.19/3.43      ((((k1_xboole_0) != (k1_xboole_0))
% 3.19/3.43        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C))),
% 3.19/3.43      inference('demod', [status(thm)], ['16', '17'])).
% 3.19/3.43  thf('19', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)),
% 3.19/3.43      inference('simplify', [status(thm)], ['18'])).
% 3.19/3.43  thf(t45_xboole_1, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( r1_tarski @ A @ B ) =>
% 3.19/3.43       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 3.19/3.43  thf('20', plain,
% 3.19/3.43      (![X13 : $i, X14 : $i]:
% 3.19/3.43         (((X14) = (k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))
% 3.19/3.43          | ~ (r1_tarski @ X13 @ X14))),
% 3.19/3.43      inference('cnf', [status(esa)], [t45_xboole_1])).
% 3.19/3.43  thf('21', plain,
% 3.19/3.43      (((sk_C)
% 3.19/3.43         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 3.19/3.43            (k4_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))))),
% 3.19/3.43      inference('sup-', [status(thm)], ['19', '20'])).
% 3.19/3.43  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(dt_k3_subset_1, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.19/3.43       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.19/3.43  thf('23', plain,
% 3.19/3.43      (![X41 : $i, X42 : $i]:
% 3.19/3.43         ((m1_subset_1 @ (k3_subset_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41))
% 3.19/3.43          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 3.19/3.43  thf('24', plain,
% 3.19/3.43      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 3.19/3.43      inference('sup-', [status(thm)], ['22', '23'])).
% 3.19/3.43  thf('25', plain,
% 3.19/3.43      (![X39 : $i, X40 : $i]:
% 3.19/3.43         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 3.19/3.43          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 3.19/3.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.19/3.43  thf('26', plain,
% 3.19/3.43      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 3.19/3.43         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['24', '25'])).
% 3.19/3.43  thf('27', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(involutiveness_k3_subset_1, axiom,
% 3.19/3.43    (![A:$i,B:$i]:
% 3.19/3.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.19/3.43       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 3.19/3.43  thf('28', plain,
% 3.19/3.43      (![X43 : $i, X44 : $i]:
% 3.19/3.43         (((k3_subset_1 @ X44 @ (k3_subset_1 @ X44 @ X43)) = (X43))
% 3.19/3.43          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 3.19/3.43      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.19/3.43  thf('29', plain,
% 3.19/3.43      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 3.19/3.43      inference('sup-', [status(thm)], ['27', '28'])).
% 3.19/3.43  thf('30', plain,
% 3.19/3.43      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 3.19/3.43      inference('demod', [status(thm)], ['26', '29'])).
% 3.19/3.43  thf('31', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.19/3.43           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.19/3.43  thf('32', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ sk_B @ X0)
% 3.19/3.43           = (k4_xboole_0 @ sk_A @ 
% 3.19/3.43              (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)))),
% 3.19/3.43      inference('sup+', [status(thm)], ['30', '31'])).
% 3.19/3.43  thf('33', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_B @ 
% 3.19/3.43         (k4_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_B)))
% 3.19/3.43         = (k4_xboole_0 @ sk_A @ sk_C))),
% 3.19/3.43      inference('sup+', [status(thm)], ['21', '32'])).
% 3.19/3.43  thf('34', plain,
% 3.19/3.43      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['0', '1'])).
% 3.19/3.43  thf('35', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_B @ 
% 3.19/3.43         (k4_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_B)))
% 3.19/3.43         = (k3_subset_1 @ sk_A @ sk_C))),
% 3.19/3.43      inference('demod', [status(thm)], ['33', '34'])).
% 3.19/3.43  thf('36', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('37', plain,
% 3.19/3.43      (![X41 : $i, X42 : $i]:
% 3.19/3.43         ((m1_subset_1 @ (k3_subset_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41))
% 3.19/3.43          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 3.19/3.43      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 3.19/3.43  thf('38', plain,
% 3.19/3.43      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 3.19/3.43      inference('sup-', [status(thm)], ['36', '37'])).
% 3.19/3.43  thf('39', plain,
% 3.19/3.43      (![X39 : $i, X40 : $i]:
% 3.19/3.43         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 3.19/3.43          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 3.19/3.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.19/3.43  thf('40', plain,
% 3.19/3.43      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 3.19/3.43         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['38', '39'])).
% 3.19/3.43  thf('41', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('42', plain,
% 3.19/3.43      (![X43 : $i, X44 : $i]:
% 3.19/3.43         (((k3_subset_1 @ X44 @ (k3_subset_1 @ X44 @ X43)) = (X43))
% 3.19/3.43          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 3.19/3.43      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.19/3.43  thf('43', plain,
% 3.19/3.43      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 3.19/3.43      inference('sup-', [status(thm)], ['41', '42'])).
% 3.19/3.43  thf('44', plain,
% 3.19/3.43      (((sk_C) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 3.19/3.43      inference('demod', [status(thm)], ['40', '43'])).
% 3.19/3.43  thf('45', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.19/3.43           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.19/3.43  thf('46', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ sk_C @ X0)
% 3.19/3.43           = (k4_xboole_0 @ sk_A @ 
% 3.19/3.43              (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ X0)))),
% 3.19/3.43      inference('sup+', [status(thm)], ['44', '45'])).
% 3.19/3.43  thf('47', plain,
% 3.19/3.43      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 3.19/3.43      inference('demod', [status(thm)], ['26', '29'])).
% 3.19/3.43  thf('48', plain,
% 3.19/3.43      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 3.19/3.43           = (k3_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ 
% 3.19/3.43              (k4_xboole_0 @ X15 @ X17)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t53_xboole_1])).
% 3.19/3.43  thf('49', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ sk_A @ 
% 3.19/3.43           (k2_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))
% 3.19/3.43           = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B))),
% 3.19/3.43      inference('sup+', [status(thm)], ['47', '48'])).
% 3.19/3.43  thf('50', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))
% 3.19/3.43         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ 
% 3.19/3.43            sk_B))),
% 3.19/3.43      inference('sup+', [status(thm)], ['46', '49'])).
% 3.19/3.43  thf('51', plain,
% 3.19/3.43      (((sk_C) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 3.19/3.43      inference('demod', [status(thm)], ['40', '43'])).
% 3.19/3.43  thf('52', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))
% 3.19/3.43         = (k3_xboole_0 @ sk_C @ sk_B))),
% 3.19/3.43      inference('demod', [status(thm)], ['50', '51'])).
% 3.19/3.43  thf('53', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf(symmetry_r1_xboole_0, axiom,
% 3.19/3.43    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 3.19/3.43  thf('54', plain,
% 3.19/3.43      (![X3 : $i, X4 : $i]:
% 3.19/3.43         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 3.19/3.43      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.19/3.43  thf('55', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 3.19/3.43      inference('sup-', [status(thm)], ['53', '54'])).
% 3.19/3.43  thf('56', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 3.19/3.43      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.19/3.43  thf('57', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['55', '56'])).
% 3.19/3.43  thf('58', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['52', '57'])).
% 3.19/3.43  thf('59', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['8', '11'])).
% 3.19/3.43  thf(t22_xboole_1, axiom,
% 3.19/3.43    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 3.19/3.43  thf('60', plain,
% 3.19/3.43      (![X5 : $i, X6 : $i]:
% 3.19/3.43         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 3.19/3.43      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.19/3.43  thf('61', plain,
% 3.19/3.43      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 3.19/3.43           = (k3_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ 
% 3.19/3.43              (k4_xboole_0 @ X15 @ X17)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t53_xboole_1])).
% 3.19/3.43  thf('62', plain,
% 3.19/3.43      (![X5 : $i, X6 : $i]:
% 3.19/3.43         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 3.19/3.43      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.19/3.43  thf('63', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.43         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 3.19/3.43           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.19/3.43           = (k4_xboole_0 @ X2 @ X1))),
% 3.19/3.43      inference('sup+', [status(thm)], ['61', '62'])).
% 3.19/3.43  thf('64', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 3.19/3.43           = (k4_xboole_0 @ X1 @ X0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['60', '63'])).
% 3.19/3.43  thf('65', plain,
% 3.19/3.43      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 3.19/3.43         k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.19/3.43      inference('sup+', [status(thm)], ['59', '64'])).
% 3.19/3.43  thf('66', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['8', '11'])).
% 3.19/3.43  thf('67', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['8', '11'])).
% 3.19/3.43  thf('68', plain,
% 3.19/3.43      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['65', '66', '67'])).
% 3.19/3.43  thf('69', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.19/3.43           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.19/3.43  thf('70', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['55', '56'])).
% 3.19/3.43  thf('71', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['8', '11'])).
% 3.19/3.43  thf('72', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.19/3.43           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.19/3.43  thf('73', plain,
% 3.19/3.43      (![X5 : $i, X6 : $i]:
% 3.19/3.43         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 3.19/3.43      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.19/3.43  thf('74', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.43         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.19/3.43          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['13', '14'])).
% 3.19/3.43  thf('75', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.43         (((k4_xboole_0 @ X2 @ X0) != (k1_xboole_0))
% 3.19/3.43          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['73', '74'])).
% 3.19/3.43  thf('76', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.19/3.43         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.19/3.43          | (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 3.19/3.43             (k3_xboole_0 @ X0 @ X3)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['72', '75'])).
% 3.19/3.43  thf('77', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.19/3.43           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.19/3.43  thf('78', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.19/3.43         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.19/3.43          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 3.19/3.43             (k3_xboole_0 @ X0 @ X3)))),
% 3.19/3.43      inference('demod', [status(thm)], ['76', '77'])).
% 3.19/3.43  thf('79', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (((k1_xboole_0) != (k1_xboole_0))
% 3.19/3.43          | (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 3.19/3.43             (k3_xboole_0 @ sk_C @ X0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['71', '78'])).
% 3.19/3.43  thf('80', plain,
% 3.19/3.43      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['8', '11'])).
% 3.19/3.43  thf('81', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (((k1_xboole_0) != (k1_xboole_0))
% 3.19/3.43          | (r1_tarski @ k1_xboole_0 @ (k3_xboole_0 @ sk_C @ X0)))),
% 3.19/3.43      inference('demod', [status(thm)], ['79', '80'])).
% 3.19/3.43  thf('82', plain,
% 3.19/3.43      (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k3_xboole_0 @ sk_C @ X0))),
% 3.19/3.43      inference('simplify', [status(thm)], ['81'])).
% 3.19/3.43  thf('83', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 3.19/3.43      inference('sup+', [status(thm)], ['70', '82'])).
% 3.19/3.43  thf('84', plain,
% 3.19/3.43      (![X7 : $i, X9 : $i]:
% 3.19/3.43         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 3.19/3.43      inference('cnf', [status(esa)], [t37_xboole_1])).
% 3.19/3.43  thf('85', plain,
% 3.19/3.43      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['83', '84'])).
% 3.19/3.43  thf('86', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.19/3.43           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.19/3.43  thf('87', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.19/3.43           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.19/3.43      inference('sup+', [status(thm)], ['85', '86'])).
% 3.19/3.43  thf('88', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.19/3.43         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 3.19/3.43           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.19/3.43           = (k4_xboole_0 @ X2 @ X1))),
% 3.19/3.43      inference('sup+', [status(thm)], ['61', '62'])).
% 3.19/3.43  thf('89', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 3.19/3.43           (k4_xboole_0 @ k1_xboole_0 @ X0))
% 3.19/3.43           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['87', '88'])).
% 3.19/3.43  thf('90', plain,
% 3.19/3.43      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['83', '84'])).
% 3.19/3.43  thf('91', plain,
% 3.19/3.43      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['83', '84'])).
% 3.19/3.43  thf('92', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 3.19/3.43           = (k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['89', '90', '91'])).
% 3.19/3.43  thf('93', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.19/3.43           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.19/3.43      inference('sup+', [status(thm)], ['85', '86'])).
% 3.19/3.43  thf('94', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 3.19/3.43           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['92', '93'])).
% 3.19/3.43  thf('95', plain,
% 3.19/3.43      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['83', '84'])).
% 3.19/3.43  thf('96', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 3.19/3.43           = (k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['94', '95'])).
% 3.19/3.43  thf('97', plain,
% 3.19/3.43      (![X7 : $i, X8 : $i]:
% 3.19/3.43         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t37_xboole_1])).
% 3.19/3.43  thf('98', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (((k1_xboole_0) != (k1_xboole_0))
% 3.19/3.43          | (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['96', '97'])).
% 3.19/3.43  thf('99', plain,
% 3.19/3.43      (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 3.19/3.43      inference('simplify', [status(thm)], ['98'])).
% 3.19/3.43  thf('100', plain,
% 3.19/3.43      (![X13 : $i, X14 : $i]:
% 3.19/3.43         (((X14) = (k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))
% 3.19/3.43          | ~ (r1_tarski @ X13 @ X14))),
% 3.19/3.43      inference('cnf', [status(esa)], [t45_xboole_1])).
% 3.19/3.43  thf('101', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.19/3.43           = (k2_xboole_0 @ k1_xboole_0 @ 
% 3.19/3.43              (k4_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['99', '100'])).
% 3.19/3.43  thf('102', plain,
% 3.19/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.19/3.43           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.19/3.43  thf('103', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 3.19/3.43           = (k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['89', '90', '91'])).
% 3.19/3.43  thf('104', plain,
% 3.19/3.43      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.19/3.43      inference('demod', [status(thm)], ['101', '102', '103'])).
% 3.19/3.43  thf('105', plain,
% 3.19/3.43      (![X7 : $i, X8 : $i]:
% 3.19/3.43         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 3.19/3.43      inference('cnf', [status(esa)], [t37_xboole_1])).
% 3.19/3.43  thf('106', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 3.19/3.43      inference('sup-', [status(thm)], ['104', '105'])).
% 3.19/3.43  thf('107', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.19/3.43      inference('simplify', [status(thm)], ['106'])).
% 3.19/3.43  thf('108', plain,
% 3.19/3.43      (![X13 : $i, X14 : $i]:
% 3.19/3.43         (((X14) = (k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))
% 3.19/3.43          | ~ (r1_tarski @ X13 @ X14))),
% 3.19/3.43      inference('cnf', [status(esa)], [t45_xboole_1])).
% 3.19/3.43  thf('109', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['107', '108'])).
% 3.19/3.43  thf('110', plain,
% 3.19/3.43      (![X0 : $i, X1 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ X1 @ X0)
% 3.19/3.43           = (k2_xboole_0 @ k1_xboole_0 @ 
% 3.19/3.43              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))))),
% 3.19/3.43      inference('sup+', [status(thm)], ['69', '109'])).
% 3.19/3.43  thf('111', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 3.19/3.43           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.19/3.43      inference('sup+', [status(thm)], ['68', '110'])).
% 3.19/3.43  thf('112', plain,
% 3.19/3.43      (![X0 : $i]:
% 3.19/3.43         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.19/3.43      inference('sup-', [status(thm)], ['107', '108'])).
% 3.19/3.43  thf('113', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 3.19/3.43      inference('sup+', [status(thm)], ['111', '112'])).
% 3.19/3.43  thf('114', plain, (((sk_B) = (k3_subset_1 @ sk_A @ sk_C))),
% 3.19/3.43      inference('demod', [status(thm)], ['35', '58', '113'])).
% 3.19/3.43  thf('115', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C))),
% 3.19/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.19/3.43  thf('116', plain, ($false),
% 3.19/3.43      inference('simplify_reflect-', [status(thm)], ['114', '115'])).
% 3.19/3.43  
% 3.19/3.43  % SZS output end Refutation
% 3.19/3.43  
% 3.19/3.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
