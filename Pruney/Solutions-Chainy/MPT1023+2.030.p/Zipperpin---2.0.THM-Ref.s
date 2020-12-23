%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kaKnoNxBmc

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 118 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  595 (2455 expanded)
%              Number of equality atoms :   10 (  54 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X15 @ X12 )
      | ( r2_hidden @ ( sk_E @ X12 @ X15 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['12','13'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    m1_subset_1 @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X16: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X16 )
        = ( k1_funct_1 @ sk_D @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
    = ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X15 @ X12 )
      | ( ( k1_funct_1 @ X15 @ ( sk_E @ X12 @ X15 @ X13 ) )
       != ( k1_funct_1 @ X12 @ ( sk_E @ X12 @ X15 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kaKnoNxBmc
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 95 iterations in 0.109s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.57  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.57  thf(t113_funct_2, conjecture,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.57       ( ![D:$i]:
% 0.20/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.57           ( ( ![E:$i]:
% 0.20/0.57               ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.57                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.20/0.57             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.57          ( ![D:$i]:
% 0.20/0.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.57              ( ( ![E:$i]:
% 0.20/0.57                  ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.57                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.20/0.57                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 0.20/0.57  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t18_funct_2, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.57       ( ![D:$i]:
% 0.20/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.57           ( ( ![E:$i]:
% 0.20/0.57               ( ( r2_hidden @ E @ A ) =>
% 0.20/0.57                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.20/0.57             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.57         (~ (v1_funct_1 @ X12)
% 0.20/0.57          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.20/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.20/0.57          | (r2_relset_1 @ X13 @ X14 @ X15 @ X12)
% 0.20/0.57          | (r2_hidden @ (sk_E @ X12 @ X15 @ X13) @ X13)
% 0.20/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.20/0.57          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.20/0.57          | ~ (v1_funct_1 @ X15))),
% 0.20/0.57      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_funct_1 @ X0)
% 0.20/0.57          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.57          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.20/0.57          | (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 0.20/0.57          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.20/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_funct_1 @ X0)
% 0.20/0.57          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.57          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.20/0.57          | (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D))),
% 0.20/0.57      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.57        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)
% 0.20/0.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.57        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.57  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.57        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.57  thf('13', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('14', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)),
% 0.20/0.57      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf(d2_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X3 : $i, X4 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.57          | (m1_subset_1 @ X3 @ X4)
% 0.20/0.57          | (v1_xboole_0 @ X4))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (((v1_xboole_0 @ sk_A)
% 0.20/0.57        | (m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('17', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)),
% 0.20/0.57      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf(d10_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.57  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.57  thf(t3_subset, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X6 : $i, X8 : $i]:
% 0.20/0.57         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.57  thf('21', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.57  thf(t5_subset, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.57          | ~ (v1_xboole_0 @ X11)
% 0.20/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.57  thf('24', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.57      inference('sup-', [status(thm)], ['17', '23'])).
% 0.20/0.57  thf('25', plain, ((m1_subset_1 @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)),
% 0.20/0.57      inference('clc', [status(thm)], ['16', '24'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (![X16 : $i]:
% 0.20/0.57         (((k1_funct_1 @ sk_C @ X16) = (k1_funct_1 @ sk_D @ X16))
% 0.20/0.57          | ~ (m1_subset_1 @ X16 @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (((k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.20/0.57         = (k1_funct_1 @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.57         (~ (v1_funct_1 @ X12)
% 0.20/0.57          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.20/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.20/0.57          | (r2_relset_1 @ X13 @ X14 @ X15 @ X12)
% 0.20/0.57          | ((k1_funct_1 @ X15 @ (sk_E @ X12 @ X15 @ X13))
% 0.20/0.57              != (k1_funct_1 @ X12 @ (sk_E @ X12 @ X15 @ X13)))
% 0.20/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.20/0.57          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.20/0.57          | ~ (v1_funct_1 @ X15))),
% 0.20/0.57      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.20/0.57            != (k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A)))
% 0.20/0.57          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.57          | (r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D)
% 0.20/0.57          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.57          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.20/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A))
% 0.20/0.57            != (k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A)))
% 0.20/0.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.57          | (r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D)
% 0.20/0.57          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.57          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.57          | (r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D)
% 0.20/0.57          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.20/0.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ X0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.57        | (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.57        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '33'])).
% 0.20/0.57  thf('35', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('38', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.20/0.57      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.20/0.57  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.43/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
