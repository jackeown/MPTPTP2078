%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ZQjNKLz05

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 127 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  630 (2657 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t66_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
           => ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_relset_1 @ X1 @ X2 @ X3 @ X0 )
      | ( r2_hidden @ ( sk_E @ X0 @ X3 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_hidden @ ( sk_E @ sk_D @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C @ sk_D )
    | ( r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X5 @ ( k1_tarski @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ ( k1_tarski @ X7 ) ) ) )
      | ( ( k1_funct_1 @ X6 @ X4 )
        = X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ X0 )
        = sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ X0 )
        = sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_relset_1 @ X1 @ X2 @ X3 @ X0 )
      | ( ( k1_funct_1 @ X3 @ ( sk_E @ X0 @ X3 @ X1 ) )
       != ( k1_funct_1 @ X0 @ ( sk_E @ X0 @ X3 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
       != sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['12','13'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X5 @ ( k1_tarski @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ ( k1_tarski @ X7 ) ) ) )
      | ( ( k1_funct_1 @ X6 @ X4 )
        = X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = sk_B )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_D @ sk_C @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_B != sk_B )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['23','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_D @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ZQjNKLz05
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:34:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 22 iterations in 0.017s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.48  thf(t66_funct_2, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.48         ( m1_subset_1 @
% 0.22/0.48           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.48       ( ![D:$i]:
% 0.22/0.48         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.48             ( m1_subset_1 @
% 0.22/0.48               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.48           ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.48            ( m1_subset_1 @
% 0.22/0.48              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.48          ( ![D:$i]:
% 0.22/0.48            ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.48                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.48                ( m1_subset_1 @
% 0.22/0.48                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.48              ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t66_funct_2])).
% 0.22/0.48  thf('0', plain, (~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C @ sk_D)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_D @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_D @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t18_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48       ( ![D:$i]:
% 0.22/0.48         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48           ( ( ![E:$i]:
% 0.22/0.48               ( ( r2_hidden @ E @ A ) =>
% 0.22/0.48                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.22/0.48             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.48         (~ (v1_funct_1 @ X0)
% 0.22/0.48          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.22/0.48          | (r2_relset_1 @ X1 @ X2 @ X3 @ X0)
% 0.22/0.48          | (r2_hidden @ (sk_E @ X0 @ X3 @ X1) @ X1)
% 0.22/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.22/0.48          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.22/0.48          | ~ (v1_funct_1 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_funct_1 @ X0)
% 0.22/0.48          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ 
% 0.22/0.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.22/0.48          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.22/0.48          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D)
% 0.22/0.48          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.48          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_funct_1 @ X0)
% 0.22/0.48          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ 
% 0.22/0.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.22/0.48          | (r2_hidden @ (sk_E @ sk_D @ X0 @ sk_A) @ sk_A)
% 0.22/0.48          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D))),
% 0.22/0.48      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C @ sk_D)
% 0.22/0.48        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)
% 0.22/0.48        | ~ (v1_funct_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.48        | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '8'])).
% 0.22/0.48  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C @ sk_D)
% 0.22/0.48        | (r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.22/0.48  thf('13', plain, (~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C @ sk_D)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('14', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)),
% 0.22/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_D @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t65_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.48         ( m1_subset_1 @
% 0.22/0.48           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.48       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.48          | ~ (v1_funct_1 @ X6)
% 0.22/0.48          | ~ (v1_funct_2 @ X6 @ X5 @ (k1_tarski @ X7))
% 0.22/0.48          | ~ (m1_subset_1 @ X6 @ 
% 0.22/0.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ (k1_tarski @ X7))))
% 0.22/0.48          | ((k1_funct_1 @ X6 @ X4) = (X7)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_funct_2])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_funct_1 @ sk_D @ X0) = (sk_B))
% 0.22/0.48          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_funct_1 @ sk_D @ X0) = (sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (((k1_funct_1 @ sk_D @ (sk_E @ sk_D @ sk_C @ sk_A)) = (sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '20'])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.48         (~ (v1_funct_1 @ X0)
% 0.22/0.48          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.22/0.48          | (r2_relset_1 @ X1 @ X2 @ X3 @ X0)
% 0.22/0.48          | ((k1_funct_1 @ X3 @ (sk_E @ X0 @ X3 @ X1))
% 0.22/0.48              != (k1_funct_1 @ X0 @ (sk_E @ X0 @ X3 @ X1)))
% 0.22/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.22/0.48          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.22/0.48          | ~ (v1_funct_1 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A)) != (sk_B))
% 0.22/0.48          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.48          | ~ (v1_funct_2 @ sk_C @ sk_A @ X0)
% 0.22/0.48          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.48          | (r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D)
% 0.22/0.48          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.48          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.22/0.48          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain, ((r2_hidden @ (sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)),
% 0.22/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.48          | ~ (v1_funct_1 @ X6)
% 0.22/0.48          | ~ (v1_funct_2 @ X6 @ X5 @ (k1_tarski @ X7))
% 0.22/0.48          | ~ (m1_subset_1 @ X6 @ 
% 0.22/0.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ (k1_tarski @ X7))))
% 0.22/0.48          | ((k1_funct_1 @ X6 @ X4) = (X7)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_funct_2])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_funct_1 @ sk_C @ X0) = (sk_B))
% 0.22/0.48          | ~ (v1_funct_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.48          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain, ((v1_funct_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_funct_1 @ sk_C @ X0) = (sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      (((k1_funct_1 @ sk_C @ (sk_E @ sk_D @ sk_C @ sk_A)) = (sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['24', '30'])).
% 0.22/0.48  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((sk_B) != (sk_B))
% 0.22/0.48          | ~ (v1_funct_2 @ sk_C @ sk_A @ X0)
% 0.22/0.48          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.48          | (r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D)
% 0.22/0.48          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.48          | ~ (v1_funct_2 @ sk_D @ sk_A @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['23', '31', '32', '33'])).
% 0.22/0.48  thf('35', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_funct_2 @ sk_D @ sk_A @ X0)
% 0.22/0.48          | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.48          | (r2_relset_1 @ sk_A @ X0 @ sk_C @ sk_D)
% 0.22/0.48          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.22/0.48          | ~ (v1_funct_2 @ sk_C @ sk_A @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.48  thf('36', plain,
% 0.22/0.48      ((~ (v1_funct_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.48        | ~ (m1_subset_1 @ sk_C @ 
% 0.22/0.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 0.22/0.48        | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C @ sk_D)
% 0.22/0.48        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '35'])).
% 0.22/0.48  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ 
% 0.22/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('40', plain, ((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C @ sk_D)),
% 0.22/0.48      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.22/0.48  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
