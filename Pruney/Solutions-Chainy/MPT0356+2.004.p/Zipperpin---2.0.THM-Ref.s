%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K8BI1uoKph

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:17 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 238 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :  737 (1901 expanded)
%              Number of equality atoms :   61 ( 139 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t35_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
             => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('27',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup+',[status(thm)],['33','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['38','43'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('56',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('70',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['53','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('86',plain,(
    r1_tarski @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['24','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K8BI1uoKph
% 0.13/0.37  % Computer   : n020.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:53:07 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.44/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.69  % Solved by: fo/fo7.sh
% 0.44/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.69  % done 671 iterations in 0.208s
% 0.44/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.69  % SZS output start Refutation
% 0.44/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.69  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.44/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.69  thf(t35_subset_1, conjecture,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69       ( ![C:$i]:
% 0.44/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.44/0.69             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.69    (~( ![A:$i,B:$i]:
% 0.44/0.69        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69          ( ![C:$i]:
% 0.44/0.69            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69              ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.44/0.69                ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.44/0.69    inference('cnf.neg', [status(esa)], [t35_subset_1])).
% 0.44/0.69  thf('0', plain, (~ (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(dt_k3_subset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.44/0.69  thf('2', plain,
% 0.44/0.69      (![X21 : $i, X22 : $i]:
% 0.44/0.69         ((m1_subset_1 @ (k3_subset_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.44/0.69          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.44/0.69      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.44/0.69  thf('3', plain,
% 0.44/0.69      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.69  thf(d5_subset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.44/0.69  thf('4', plain,
% 0.44/0.69      (![X19 : $i, X20 : $i]:
% 0.44/0.69         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.44/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.44/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.69  thf('5', plain,
% 0.44/0.69      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.44/0.69         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.69  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(involutiveness_k3_subset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.44/0.69  thf('7', plain,
% 0.44/0.69      (![X23 : $i, X24 : $i]:
% 0.44/0.69         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 0.44/0.69          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.44/0.69      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.44/0.69  thf('8', plain,
% 0.44/0.69      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.44/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.69  thf('9', plain,
% 0.44/0.69      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('demod', [status(thm)], ['5', '8'])).
% 0.44/0.69  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('11', plain,
% 0.44/0.69      (![X19 : $i, X20 : $i]:
% 0.44/0.69         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.44/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.44/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.69  thf('12', plain,
% 0.44/0.69      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.69  thf(t48_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.69  thf('13', plain,
% 0.44/0.69      (![X14 : $i, X15 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.44/0.69           = (k3_xboole_0 @ X14 @ X15))),
% 0.44/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.69  thf('14', plain,
% 0.44/0.69      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.44/0.69         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.69      inference('sup+', [status(thm)], ['12', '13'])).
% 0.44/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.69  thf('15', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.69  thf('16', plain,
% 0.44/0.69      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.44/0.69         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.44/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.44/0.69  thf('17', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.44/0.69      inference('sup+', [status(thm)], ['9', '16'])).
% 0.44/0.69  thf('18', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.69  thf(t100_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.69  thf('19', plain,
% 0.44/0.69      (![X5 : $i, X6 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.44/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.69  thf('20', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.44/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.69  thf('21', plain,
% 0.44/0.69      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.69      inference('sup+', [status(thm)], ['17', '20'])).
% 0.44/0.69  thf('22', plain,
% 0.44/0.69      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.69  thf('23', plain,
% 0.44/0.69      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.69      inference('sup+', [status(thm)], ['21', '22'])).
% 0.44/0.69  thf('24', plain, (~ (r1_tarski @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.69      inference('demod', [status(thm)], ['0', '23'])).
% 0.44/0.69  thf('25', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('26', plain,
% 0.44/0.69      (![X21 : $i, X22 : $i]:
% 0.44/0.69         ((m1_subset_1 @ (k3_subset_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.44/0.69          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.44/0.69      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.44/0.69  thf('27', plain,
% 0.44/0.69      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.69  thf('28', plain,
% 0.44/0.69      (![X19 : $i, X20 : $i]:
% 0.44/0.69         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.44/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.44/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.69  thf('29', plain,
% 0.44/0.69      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 0.44/0.69         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.69  thf('30', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('31', plain,
% 0.44/0.69      (![X23 : $i, X24 : $i]:
% 0.44/0.69         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 0.44/0.69          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.44/0.69      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.44/0.69  thf('32', plain,
% 0.44/0.69      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.44/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.69  thf('33', plain,
% 0.44/0.69      (((sk_C) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.44/0.69      inference('demod', [status(thm)], ['29', '32'])).
% 0.44/0.69  thf(t36_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.69  thf('34', plain,
% 0.44/0.69      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.44/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.69  thf('35', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.44/0.69      inference('sup+', [status(thm)], ['33', '34'])).
% 0.44/0.69  thf(d10_xboole_0, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.69  thf('36', plain,
% 0.44/0.69      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.44/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.69  thf('37', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.44/0.69      inference('simplify', [status(thm)], ['36'])).
% 0.44/0.69  thf('38', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('39', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('40', plain,
% 0.44/0.69      (![X19 : $i, X20 : $i]:
% 0.44/0.69         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.44/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.44/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.69  thf('41', plain,
% 0.44/0.69      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.69      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.69  thf(t106_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.44/0.69       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.44/0.69  thf('42', plain,
% 0.44/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.69         ((r1_xboole_0 @ X7 @ X9)
% 0.44/0.69          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.44/0.69  thf('43', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.44/0.69          | (r1_xboole_0 @ X0 @ sk_C))),
% 0.44/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.44/0.69  thf('44', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.44/0.69      inference('sup-', [status(thm)], ['38', '43'])).
% 0.44/0.69  thf(t86_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.44/0.69       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.44/0.69  thf('45', plain,
% 0.44/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.69         (~ (r1_tarski @ X16 @ X17)
% 0.44/0.69          | ~ (r1_xboole_0 @ X16 @ X18)
% 0.44/0.69          | (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X18)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.44/0.69  thf('46', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))
% 0.44/0.69          | ~ (r1_tarski @ sk_B @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['44', '45'])).
% 0.44/0.69  thf('47', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.44/0.69      inference('sup-', [status(thm)], ['37', '46'])).
% 0.44/0.69  thf('48', plain,
% 0.44/0.69      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.44/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.69  thf('49', plain,
% 0.44/0.69      (![X2 : $i, X4 : $i]:
% 0.44/0.69         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.44/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.69  thf('50', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.44/0.69          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.44/0.69  thf('51', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.44/0.69      inference('sup-', [status(thm)], ['47', '50'])).
% 0.44/0.69  thf('52', plain,
% 0.44/0.69      (![X14 : $i, X15 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.44/0.69           = (k3_xboole_0 @ X14 @ X15))),
% 0.44/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.69  thf('53', plain,
% 0.44/0.69      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.44/0.69      inference('sup+', [status(thm)], ['51', '52'])).
% 0.44/0.69  thf('54', plain,
% 0.44/0.69      (![X14 : $i, X15 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.44/0.69           = (k3_xboole_0 @ X14 @ X15))),
% 0.44/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.69  thf('55', plain,
% 0.44/0.69      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.44/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.69  thf('56', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.44/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.69  thf('57', plain,
% 0.44/0.69      (![X2 : $i, X4 : $i]:
% 0.44/0.69         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.44/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.69  thf('58', plain,
% 0.44/0.69      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.69  thf('59', plain,
% 0.44/0.69      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['55', '58'])).
% 0.44/0.69  thf('60', plain,
% 0.44/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['54', '59'])).
% 0.44/0.69  thf('61', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.69  thf('62', plain,
% 0.44/0.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['60', '61'])).
% 0.44/0.69  thf('63', plain,
% 0.44/0.69      (![X5 : $i, X6 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.44/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.69  thf('64', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['62', '63'])).
% 0.44/0.69  thf('65', plain,
% 0.44/0.69      (![X14 : $i, X15 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.44/0.69           = (k3_xboole_0 @ X14 @ X15))),
% 0.44/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.69  thf('66', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.44/0.69           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['64', '65'])).
% 0.44/0.69  thf('67', plain,
% 0.44/0.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['60', '61'])).
% 0.44/0.69  thf('68', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['66', '67'])).
% 0.44/0.69  thf('69', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['62', '63'])).
% 0.44/0.69  thf(t3_boole, axiom,
% 0.44/0.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.69  thf('70', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.44/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.69  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['69', '70'])).
% 0.44/0.69  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['68', '71'])).
% 0.44/0.69  thf('73', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.44/0.69      inference('demod', [status(thm)], ['53', '72'])).
% 0.44/0.69  thf('74', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.44/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.69  thf('75', plain,
% 0.44/0.69      (((k4_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_C @ k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['73', '74'])).
% 0.44/0.69  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['69', '70'])).
% 0.44/0.69  thf('77', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.44/0.69      inference('demod', [status(thm)], ['75', '76'])).
% 0.44/0.69  thf('78', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.44/0.69      inference('simplify', [status(thm)], ['36'])).
% 0.44/0.69  thf('79', plain,
% 0.44/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.69         ((r1_xboole_0 @ X7 @ X9)
% 0.44/0.69          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.44/0.69  thf('80', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.44/0.69      inference('sup-', [status(thm)], ['78', '79'])).
% 0.44/0.69  thf('81', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.44/0.69      inference('sup+', [status(thm)], ['77', '80'])).
% 0.44/0.69  thf('82', plain,
% 0.44/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.69         (~ (r1_tarski @ X16 @ X17)
% 0.44/0.69          | ~ (r1_xboole_0 @ X16 @ X18)
% 0.44/0.69          | (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X18)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.44/0.69  thf('83', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((r1_tarski @ sk_C @ (k4_xboole_0 @ X0 @ sk_B))
% 0.44/0.69          | ~ (r1_tarski @ sk_C @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['81', '82'])).
% 0.44/0.69  thf('84', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.69      inference('sup-', [status(thm)], ['35', '83'])).
% 0.44/0.69  thf('85', plain,
% 0.44/0.69      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.69      inference('sup+', [status(thm)], ['17', '20'])).
% 0.44/0.69  thf('86', plain, ((r1_tarski @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.44/0.69      inference('demod', [status(thm)], ['84', '85'])).
% 0.44/0.69  thf('87', plain, ($false), inference('demod', [status(thm)], ['24', '86'])).
% 0.44/0.69  
% 0.44/0.69  % SZS output end Refutation
% 0.44/0.69  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
