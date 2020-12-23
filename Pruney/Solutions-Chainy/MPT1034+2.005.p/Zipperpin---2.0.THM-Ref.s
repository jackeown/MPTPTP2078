%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZDEtGLRg3h

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  93 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  513 (1492 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(t143_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
             => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X16 = X13 )
      | ~ ( r1_partfun1 @ X16 @ X13 )
      | ~ ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_partfun1 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ( X0 = sk_C ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( X0 = sk_C )
      | ~ ( r1_partfun1 @ X0 @ sk_C )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ~ ( r1_partfun1 @ sk_B_1 @ sk_C )
    | ( sk_B_1 = sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B_1 = sk_C ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( ( k11_relat_1 @ B @ D )
                  = ( k11_relat_1 @ C @ D ) ) )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) )
      | ( r2_relset_1 @ X8 @ X8 @ X9 @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_A )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_B_1 = sk_C ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_relset_1 @ X3 @ X4 @ X5 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZDEtGLRg3h
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 35 iterations in 0.024s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.20/0.48  thf(t143_funct_2, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.48             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48           ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.48            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48          ( ![C:$i]:
% 0.20/0.48            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.48                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48              ( ( r1_partfun1 @ B @ C ) => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t143_funct_2])).
% 0.20/0.48  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc5_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.48             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.20/0.48          | (v1_partfun1 @ X10 @ X11)
% 0.20/0.48          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.20/0.48          | ~ (v1_funct_1 @ X10)
% 0.20/0.48          | (v1_xboole_0 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_A)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.48        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.20/0.48        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t148_partfun1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( ![D:$i]:
% 0.20/0.48         ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.20/0.48               ( r1_partfun1 @ C @ D ) ) =>
% 0.20/0.48             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (v1_funct_1 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.48          | ((X16) = (X13))
% 0.20/0.48          | ~ (r1_partfun1 @ X16 @ X13)
% 0.20/0.48          | ~ (v1_partfun1 @ X13 @ X14)
% 0.20/0.48          | ~ (v1_partfun1 @ X16 @ X14)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.48          | ~ (v1_funct_1 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.48          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.48          | ((X0) = (sk_C))
% 0.20/0.48          | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.48          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.48          | ((X0) = (sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ sk_A)
% 0.20/0.48          | ((X0) = (sk_C))
% 0.20/0.48          | ~ (r1_partfun1 @ X0 @ sk_C)
% 0.20/0.48          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.48          | ~ (v1_funct_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((~ (v1_funct_1 @ sk_B_1)
% 0.20/0.48        | ~ (v1_partfun1 @ sk_B_1 @ sk_A)
% 0.20/0.48        | ~ (r1_partfun1 @ sk_B_1 @ sk_C)
% 0.20/0.48        | ((sk_B_1) = (sk_C))
% 0.20/0.48        | (v1_xboole_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '13'])).
% 0.20/0.48  thf('15', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain, ((r1_partfun1 @ sk_B_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((~ (v1_partfun1 @ sk_B_1 @ sk_A)
% 0.20/0.48        | ((sk_B_1) = (sk_C))
% 0.20/0.48        | (v1_xboole_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.20/0.48          | (v1_partfun1 @ X10 @ X11)
% 0.20/0.48          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.20/0.48          | ~ (v1_funct_1 @ X10)
% 0.20/0.48          | (v1_xboole_0 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_A)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.48        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.20/0.48        | (v1_partfun1 @ sk_B_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B_1 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.48  thf('24', plain, (((v1_xboole_0 @ sk_A) | ((sk_B_1) = (sk_C)))),
% 0.20/0.48      inference('clc', [status(thm)], ['17', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t54_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.48           ( ( ![D:$i]:
% 0.20/0.48               ( ( r2_hidden @ D @ A ) =>
% 0.20/0.48                 ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.20/0.48             ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8)))
% 0.20/0.48          | (r2_relset_1 @ X8 @ X8 @ X9 @ X7)
% 0.20/0.48          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X8)
% 0.20/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X8))))),
% 0.20/0.48      inference('cnf', [status(esa)], [t54_relset_1])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.48          | (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_A)
% 0.20/0.48          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (((r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_C)
% 0.20/0.48        | (r2_hidden @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.48  thf('30', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, (((sk_B_1) = (sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(reflexivity_r2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((r2_relset_1 @ X3 @ X4 @ X5 @ X5)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.20/0.48      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.48      inference('condensation', [status(thm)], ['36'])).
% 0.20/0.48  thf('38', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.48  thf('39', plain, ($false),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '34', '38'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
