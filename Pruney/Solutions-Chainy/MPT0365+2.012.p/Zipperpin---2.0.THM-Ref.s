%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tHFWynI2SL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:07 EST 2020

% Result     : Theorem 9.74s
% Output     : Refutation 9.74s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 181 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  833 (1789 expanded)
%              Number of equality atoms :   71 ( 137 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_xboole_0 @ X53 @ ( k3_subset_1 @ X52 @ X51 ) )
      | ( r1_tarski @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t44_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X47: $i,X48: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X47 @ X48 ) @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['6','9'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('12',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X47: $i,X48: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X47 @ X48 ) @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('26',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('30',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k3_subset_1 @ X50 @ ( k3_subset_1 @ X50 @ X49 ) )
        = X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53','58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','60'])).

thf('62',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','66','67'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X5 )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_B
    = ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['12','68','73'])).

thf('75',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tHFWynI2SL
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 9.74/9.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.74/9.95  % Solved by: fo/fo7.sh
% 9.74/9.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.74/9.95  % done 14242 iterations in 9.502s
% 9.74/9.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.74/9.95  % SZS output start Refutation
% 9.74/9.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.74/9.95  thf(sk_B_type, type, sk_B: $i).
% 9.74/9.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.74/9.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.74/9.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.74/9.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.74/9.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.74/9.95  thf(sk_A_type, type, sk_A: $i).
% 9.74/9.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.74/9.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.74/9.95  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.74/9.95  thf(sk_C_type, type, sk_C: $i).
% 9.74/9.95  thf(t46_subset_1, conjecture,
% 9.74/9.95    (![A:$i,B:$i]:
% 9.74/9.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.74/9.95       ( ![C:$i]:
% 9.74/9.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.74/9.95           ( ( ( r1_xboole_0 @ B @ C ) & 
% 9.74/9.95               ( r1_xboole_0 @
% 9.74/9.95                 ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 9.74/9.95             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 9.74/9.95  thf(zf_stmt_0, negated_conjecture,
% 9.74/9.95    (~( ![A:$i,B:$i]:
% 9.74/9.95        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.74/9.95          ( ![C:$i]:
% 9.74/9.95            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.74/9.95              ( ( ( r1_xboole_0 @ B @ C ) & 
% 9.74/9.95                  ( r1_xboole_0 @
% 9.74/9.95                    ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 9.74/9.95                ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 9.74/9.95    inference('cnf.neg', [status(esa)], [t46_subset_1])).
% 9.74/9.95  thf('0', plain,
% 9.74/9.95      ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ (k3_subset_1 @ sk_A @ sk_C))),
% 9.74/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.95  thf(symmetry_r1_xboole_0, axiom,
% 9.74/9.95    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 9.74/9.95  thf('1', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i]:
% 9.74/9.95         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 9.74/9.95      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 9.74/9.95  thf('2', plain,
% 9.74/9.95      ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))),
% 9.74/9.95      inference('sup-', [status(thm)], ['0', '1'])).
% 9.74/9.95  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.74/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.95  thf(t44_subset_1, axiom,
% 9.74/9.95    (![A:$i,B:$i]:
% 9.74/9.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.74/9.95       ( ![C:$i]:
% 9.74/9.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.74/9.95           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 9.74/9.95             ( r1_tarski @ B @ C ) ) ) ) ))).
% 9.74/9.95  thf('4', plain,
% 9.74/9.95      (![X51 : $i, X52 : $i, X53 : $i]:
% 9.74/9.95         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52))
% 9.74/9.95          | ~ (r1_xboole_0 @ X53 @ (k3_subset_1 @ X52 @ X51))
% 9.74/9.95          | (r1_tarski @ X53 @ X51)
% 9.74/9.95          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X52)))),
% 9.74/9.95      inference('cnf', [status(esa)], [t44_subset_1])).
% 9.74/9.95  thf('5', plain,
% 9.74/9.95      (![X0 : $i]:
% 9.74/9.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 9.74/9.95          | (r1_tarski @ X0 @ sk_B)
% 9.74/9.95          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 9.74/9.95      inference('sup-', [status(thm)], ['3', '4'])).
% 9.74/9.95  thf('6', plain,
% 9.74/9.95      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)
% 9.74/9.95        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A)))),
% 9.74/9.95      inference('sup-', [status(thm)], ['2', '5'])).
% 9.74/9.95  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 9.74/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.95  thf(dt_k3_subset_1, axiom,
% 9.74/9.95    (![A:$i,B:$i]:
% 9.74/9.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.74/9.95       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.74/9.95  thf('8', plain,
% 9.74/9.95      (![X47 : $i, X48 : $i]:
% 9.74/9.95         ((m1_subset_1 @ (k3_subset_1 @ X47 @ X48) @ (k1_zfmisc_1 @ X47))
% 9.74/9.95          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 9.74/9.95      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.74/9.95  thf('9', plain,
% 9.74/9.95      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 9.74/9.95      inference('sup-', [status(thm)], ['7', '8'])).
% 9.74/9.95  thf('10', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 9.74/9.95      inference('demod', [status(thm)], ['6', '9'])).
% 9.74/9.95  thf(t45_xboole_1, axiom,
% 9.74/9.95    (![A:$i,B:$i]:
% 9.74/9.95     ( ( r1_tarski @ A @ B ) =>
% 9.74/9.95       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 9.74/9.95  thf('11', plain,
% 9.74/9.95      (![X9 : $i, X10 : $i]:
% 9.74/9.95         (((X10) = (k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))
% 9.74/9.95          | ~ (r1_tarski @ X9 @ X10))),
% 9.74/9.95      inference('cnf', [status(esa)], [t45_xboole_1])).
% 9.74/9.95  thf('12', plain,
% 9.74/9.95      (((sk_B)
% 9.74/9.95         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 9.74/9.95            (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 9.74/9.95      inference('sup-', [status(thm)], ['10', '11'])).
% 9.74/9.95  thf('13', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 9.74/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.95  thf(d5_subset_1, axiom,
% 9.74/9.95    (![A:$i,B:$i]:
% 9.74/9.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.74/9.95       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.74/9.95  thf('14', plain,
% 9.74/9.95      (![X45 : $i, X46 : $i]:
% 9.74/9.95         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 9.74/9.95          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 9.74/9.95      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.74/9.95  thf('15', plain,
% 9.74/9.95      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 9.74/9.95      inference('sup-', [status(thm)], ['13', '14'])).
% 9.74/9.95  thf(t41_xboole_1, axiom,
% 9.74/9.95    (![A:$i,B:$i,C:$i]:
% 9.74/9.95     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 9.74/9.95       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.74/9.95  thf('16', plain,
% 9.74/9.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 9.74/9.95           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 9.74/9.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.74/9.95  thf('17', plain,
% 9.74/9.95      (![X0 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ X0)
% 9.74/9.95           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 9.74/9.95      inference('sup+', [status(thm)], ['15', '16'])).
% 9.74/9.95  thf(t3_boole, axiom,
% 9.74/9.95    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 9.74/9.95  thf('18', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 9.74/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.74/9.95  thf(t48_xboole_1, axiom,
% 9.74/9.95    (![A:$i,B:$i]:
% 9.74/9.95     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.74/9.95  thf('19', plain,
% 9.74/9.95      (![X11 : $i, X12 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 9.74/9.95           = (k3_xboole_0 @ X11 @ X12))),
% 9.74/9.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.74/9.95  thf('20', plain,
% 9.74/9.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 9.74/9.95      inference('sup+', [status(thm)], ['18', '19'])).
% 9.74/9.95  thf(t2_boole, axiom,
% 9.74/9.95    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 9.74/9.95  thf('21', plain,
% 9.74/9.95      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 9.74/9.95      inference('cnf', [status(esa)], [t2_boole])).
% 9.74/9.95  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.74/9.95      inference('demod', [status(thm)], ['20', '21'])).
% 9.74/9.95  thf('23', plain,
% 9.74/9.95      (((k4_xboole_0 @ sk_A @ 
% 9.74/9.95         (k2_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_C))) = (k1_xboole_0))),
% 9.74/9.95      inference('sup+', [status(thm)], ['17', '22'])).
% 9.74/9.95  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.74/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.95  thf('25', plain,
% 9.74/9.95      (![X47 : $i, X48 : $i]:
% 9.74/9.95         ((m1_subset_1 @ (k3_subset_1 @ X47 @ X48) @ (k1_zfmisc_1 @ X47))
% 9.74/9.95          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 9.74/9.95      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.74/9.95  thf('26', plain,
% 9.74/9.95      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 9.74/9.95      inference('sup-', [status(thm)], ['24', '25'])).
% 9.74/9.95  thf('27', plain,
% 9.74/9.95      (![X45 : $i, X46 : $i]:
% 9.74/9.95         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 9.74/9.95          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 9.74/9.95      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.74/9.95  thf('28', plain,
% 9.74/9.95      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 9.74/9.95         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 9.74/9.95      inference('sup-', [status(thm)], ['26', '27'])).
% 9.74/9.95  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.74/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.95  thf(involutiveness_k3_subset_1, axiom,
% 9.74/9.95    (![A:$i,B:$i]:
% 9.74/9.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.74/9.95       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 9.74/9.95  thf('30', plain,
% 9.74/9.95      (![X49 : $i, X50 : $i]:
% 9.74/9.95         (((k3_subset_1 @ X50 @ (k3_subset_1 @ X50 @ X49)) = (X49))
% 9.74/9.95          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 9.74/9.95      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.74/9.95  thf('31', plain,
% 9.74/9.95      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 9.74/9.95      inference('sup-', [status(thm)], ['29', '30'])).
% 9.74/9.95  thf('32', plain,
% 9.74/9.95      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 9.74/9.95      inference('demod', [status(thm)], ['28', '31'])).
% 9.74/9.95  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.74/9.95      inference('demod', [status(thm)], ['20', '21'])).
% 9.74/9.95  thf('34', plain,
% 9.74/9.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 9.74/9.95           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 9.74/9.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.74/9.95  thf('35', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i]:
% 9.74/9.95         ((k1_xboole_0)
% 9.74/9.95           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.74/9.95      inference('sup+', [status(thm)], ['33', '34'])).
% 9.74/9.95  thf('36', plain,
% 9.74/9.95      (![X11 : $i, X12 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 9.74/9.95           = (k3_xboole_0 @ X11 @ X12))),
% 9.74/9.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.74/9.95  thf('37', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 9.74/9.95           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.74/9.95      inference('sup+', [status(thm)], ['35', '36'])).
% 9.74/9.95  thf('38', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 9.74/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.74/9.95  thf('39', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i]:
% 9.74/9.95         ((X1)
% 9.74/9.95           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.74/9.95      inference('demod', [status(thm)], ['37', '38'])).
% 9.74/9.95  thf('40', plain,
% 9.74/9.95      (((sk_A)
% 9.74/9.95         = (k3_xboole_0 @ sk_A @ 
% 9.74/9.95            (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 9.74/9.95      inference('sup+', [status(thm)], ['32', '39'])).
% 9.74/9.95  thf('41', plain,
% 9.74/9.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 9.74/9.95           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 9.74/9.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.74/9.95  thf('42', plain,
% 9.74/9.95      (![X11 : $i, X12 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 9.74/9.95           = (k3_xboole_0 @ X11 @ X12))),
% 9.74/9.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.74/9.95  thf('43', plain,
% 9.74/9.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 9.74/9.95           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 9.74/9.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.74/9.95  thf('44', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 9.74/9.95           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 9.74/9.95      inference('sup+', [status(thm)], ['42', '43'])).
% 9.74/9.95  thf('45', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0)
% 9.74/9.95           = (k4_xboole_0 @ X3 @ 
% 9.74/9.95              (k2_xboole_0 @ X2 @ 
% 9.74/9.95               (k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0))))),
% 9.74/9.95      inference('sup+', [status(thm)], ['41', '44'])).
% 9.74/9.95  thf('46', plain,
% 9.74/9.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 9.74/9.95           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 9.74/9.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.74/9.95  thf('47', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0)
% 9.74/9.95           = (k4_xboole_0 @ X3 @ 
% 9.74/9.95              (k2_xboole_0 @ X2 @ 
% 9.74/9.95               (k2_xboole_0 @ (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ X1)) @ X0))))),
% 9.74/9.95      inference('demod', [status(thm)], ['45', '46'])).
% 9.74/9.95  thf('48', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 9.74/9.95           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 9.74/9.95      inference('sup+', [status(thm)], ['42', '43'])).
% 9.74/9.95  thf(t53_xboole_1, axiom,
% 9.74/9.95    (![A:$i,B:$i,C:$i]:
% 9.74/9.95     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 9.74/9.95       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 9.74/9.95  thf('49', plain,
% 9.74/9.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 9.74/9.95           = (k3_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 9.74/9.95              (k4_xboole_0 @ X13 @ X15)))),
% 9.74/9.95      inference('cnf', [status(esa)], [t53_xboole_1])).
% 9.74/9.95  thf('50', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ X2 @ 
% 9.74/9.95           (k2_xboole_0 @ X3 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 9.74/9.95           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ 
% 9.74/9.95              (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 9.74/9.95      inference('sup+', [status(thm)], ['48', '49'])).
% 9.74/9.95  thf('51', plain,
% 9.74/9.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0)
% 9.74/9.95           = (k3_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ 
% 9.74/9.95              (k4_xboole_0 @ (k3_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ X1)) @ X0)))),
% 9.74/9.95      inference('demod', [status(thm)], ['47', '50'])).
% 9.74/9.95  thf('52', plain,
% 9.74/9.95      (![X0 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ 
% 9.74/9.95           (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 9.74/9.95            sk_B) @ 
% 9.74/9.95           X0)
% 9.74/9.95           = (k3_xboole_0 @ 
% 9.74/9.95              (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 9.74/9.95              (k4_xboole_0 @ sk_A @ X0)))),
% 9.74/9.95      inference('sup+', [status(thm)], ['40', '51'])).
% 9.74/9.95  thf('53', plain,
% 9.74/9.95      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 9.74/9.95      inference('demod', [status(thm)], ['28', '31'])).
% 9.74/9.95  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.74/9.95      inference('demod', [status(thm)], ['20', '21'])).
% 9.74/9.95  thf('55', plain,
% 9.74/9.95      (![X11 : $i, X12 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 9.74/9.95           = (k3_xboole_0 @ X11 @ X12))),
% 9.74/9.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.74/9.95  thf('56', plain,
% 9.74/9.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 9.74/9.95      inference('sup+', [status(thm)], ['54', '55'])).
% 9.74/9.95  thf('57', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 9.74/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.74/9.95  thf('58', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 9.74/9.95      inference('demod', [status(thm)], ['56', '57'])).
% 9.74/9.95  thf('59', plain,
% 9.74/9.95      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 9.74/9.95      inference('demod', [status(thm)], ['28', '31'])).
% 9.74/9.95  thf('60', plain,
% 9.74/9.95      (![X0 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ sk_B @ X0)
% 9.74/9.95           = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)))),
% 9.74/9.95      inference('demod', [status(thm)], ['52', '53', '58', '59'])).
% 9.74/9.95  thf('61', plain,
% 9.74/9.95      (((k4_xboole_0 @ sk_B @ 
% 9.74/9.95         (k2_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_C)))
% 9.74/9.95         = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 9.74/9.95      inference('sup+', [status(thm)], ['23', '60'])).
% 9.74/9.95  thf('62', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 9.74/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.95  thf(t83_xboole_1, axiom,
% 9.74/9.95    (![A:$i,B:$i]:
% 9.74/9.95     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.74/9.95  thf('63', plain,
% 9.74/9.95      (![X16 : $i, X17 : $i]:
% 9.74/9.95         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 9.74/9.95      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.74/9.95  thf('64', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 9.74/9.95      inference('sup-', [status(thm)], ['62', '63'])).
% 9.74/9.95  thf('65', plain,
% 9.74/9.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 9.74/9.95           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 9.74/9.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.74/9.95  thf('66', plain,
% 9.74/9.95      (![X0 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ sk_B @ X0)
% 9.74/9.95           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 9.74/9.95      inference('sup+', [status(thm)], ['64', '65'])).
% 9.74/9.95  thf('67', plain,
% 9.74/9.95      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 9.74/9.95      inference('cnf', [status(esa)], [t2_boole])).
% 9.74/9.95  thf('68', plain,
% 9.74/9.95      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 9.74/9.95      inference('demod', [status(thm)], ['61', '66', '67'])).
% 9.74/9.95  thf(t40_xboole_1, axiom,
% 9.74/9.95    (![A:$i,B:$i]:
% 9.74/9.95     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 9.74/9.95  thf('69', plain,
% 9.74/9.95      (![X4 : $i, X5 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X5)
% 9.74/9.95           = (k4_xboole_0 @ X4 @ X5))),
% 9.74/9.95      inference('cnf', [status(esa)], [t40_xboole_1])).
% 9.74/9.95  thf('70', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 9.74/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.74/9.95  thf('71', plain,
% 9.74/9.95      (![X0 : $i]:
% 9.74/9.95         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 9.74/9.95      inference('sup+', [status(thm)], ['69', '70'])).
% 9.74/9.95  thf('72', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 9.74/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.74/9.95  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.74/9.95      inference('sup+', [status(thm)], ['71', '72'])).
% 9.74/9.95  thf('74', plain, (((sk_B) = (k3_subset_1 @ sk_A @ sk_C))),
% 9.74/9.95      inference('demod', [status(thm)], ['12', '68', '73'])).
% 9.74/9.95  thf('75', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C))),
% 9.74/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.74/9.95  thf('76', plain, ($false),
% 9.74/9.95      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 9.74/9.95  
% 9.74/9.95  % SZS output end Refutation
% 9.74/9.95  
% 9.74/9.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
