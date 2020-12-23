%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qD9nericX

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 130 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  568 (1688 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t51_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
             => ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) )
    = ( k4_xboole_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X12 @ X11 ) @ ( k7_setfam_1 @ X12 @ X13 ) )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ ( k4_xboole_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( k4_xboole_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ( r2_hidden @ ( k3_subset_1 @ X12 @ X11 ) @ ( k7_setfam_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) )
    = ( k4_xboole_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('30',plain,(
    r2_hidden @ ( k4_xboole_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k7_setfam_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( k4_xboole_0 @ sk_A @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) @ ( k7_setfam_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['15','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qD9nericX
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:16:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 70 iterations in 0.037s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.50  thf(t51_setfam_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.21/0.50             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50          ( ![C:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50              ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.21/0.50                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t51_setfam_1])).
% 0.21/0.50  thf('0', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t7_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50           ( ( ![D:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.50                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.50             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.50          | (r1_tarski @ X7 @ X5)
% 0.21/0.50          | (m1_subset_1 @ (sk_D @ X5 @ X7 @ X6) @ X6)
% 0.21/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.50          | (m1_subset_1 @ (sk_D @ sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.50             (k1_zfmisc_1 @ sk_A))
% 0.21/0.50          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.50        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.50           (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf('6', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.50        (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(d5_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.50         = (k4_xboole_0 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t49_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.21/0.50             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.21/0.50          | ~ (r2_hidden @ (k3_subset_1 @ X12 @ X11) @ 
% 0.21/0.50               (k7_setfam_1 @ X12 @ X13))
% 0.21/0.50          | (r2_hidden @ X11 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.21/0.50      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ sk_C)
% 0.21/0.50          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.21/0.50               (k7_setfam_1 @ sk_A @ sk_C))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((~ (r2_hidden @ 
% 0.21/0.50           (k4_xboole_0 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.21/0.50           (k7_setfam_1 @ sk_A @ sk_C))
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.50             (k1_zfmisc_1 @ sk_A))
% 0.21/0.50        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.50        (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((~ (r2_hidden @ 
% 0.21/0.50           (k4_xboole_0 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.21/0.50           (k7_setfam_1 @ sk_A @ sk_C))
% 0.21/0.50        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.21/0.50        (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.21/0.50          | ~ (r2_hidden @ X11 @ X13)
% 0.21/0.50          | (r2_hidden @ (k3_subset_1 @ X12 @ X11) @ (k7_setfam_1 @ X12 @ X13))
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.21/0.50      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((~ (r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B)
% 0.21/0.50        | (r2_hidden @ 
% 0.21/0.50           (k3_subset_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.21/0.50           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.50          | (r1_tarski @ X7 @ X5)
% 0.21/0.50          | (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X7)
% 0.21/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.50          | (r2_hidden @ (sk_D @ sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ X0)
% 0.21/0.50          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.50        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.50  thf('26', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_B)),
% 0.21/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((r2_hidden @ 
% 0.21/0.50        (k3_subset_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.21/0.50        (k7_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.50         = (k4_xboole_0 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      ((r2_hidden @ 
% 0.21/0.50        (k4_xboole_0 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.21/0.50        (k7_setfam_1 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ (k7_setfam_1 @ sk_A @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X8 : $i, X10 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k7_setfam_1 @ sk_A @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf(l3_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.50          | (r2_hidden @ X2 @ X4)
% 0.21/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_C))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((r2_hidden @ 
% 0.21/0.50        (k4_xboole_0 @ sk_A @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A))) @ 
% 0.21/0.50        (k7_setfam_1 @ sk_A @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((r2_hidden @ (sk_D @ sk_C @ sk_B @ (k1_zfmisc_1 @ sk_A)) @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.50          | (r1_tarski @ X7 @ X5)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X5)
% 0.21/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ sk_C @ X0 @ (k1_zfmisc_1 @ sk_A)) @ sk_C)
% 0.21/0.50          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.50        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
