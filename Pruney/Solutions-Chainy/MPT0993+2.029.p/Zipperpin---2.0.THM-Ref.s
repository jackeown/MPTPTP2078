%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dBMVdAgcmd

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  466 ( 857 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t40_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ A @ C )
         => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k2_partfun1 @ X18 @ X19 @ X17 @ X20 )
        = ( k7_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['0','5','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X24 @ X21 )
      | ( ( k1_funct_1 @ X24 @ ( sk_E @ X21 @ X24 @ X22 ) )
       != ( k1_funct_1 @ X21 @ ( sk_E @ X21 @ X24 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['25','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dBMVdAgcmd
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 71 iterations in 0.037s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(t40_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( r1_tarski @ A @ C ) =>
% 0.21/0.52         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52          ( ( r1_tarski @ A @ C ) =>
% 0.21/0.52            ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t40_funct_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.21/0.52          (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.52          | ~ (v1_funct_1 @ X17)
% 0.21/0.52          | ((k2_partfun1 @ X18 @ X19 @ X17 @ X20) = (k7_relat_1 @ X17 @ X20)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t118_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.52         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.52          | (r1_tarski @ (k2_zfmisc_1 @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_C @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t3_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('11', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf(t1_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.52       ( r1_tarski @ A @ C ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.52          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.52          | (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r1_tarski @ sk_D @ X0)
% 0.21/0.52          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_C @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X6 : $i, X8 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf(cc2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         ((v4_relat_1 @ X14 @ X15)
% 0.21/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.52  thf('18', plain, ((v4_relat_1 @ sk_D @ sk_C)),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf(t209_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.21/0.52          | ~ (v4_relat_1 @ X9 @ X10)
% 0.21/0.52          | ~ (v1_relat_1 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( v1_relat_1 @ C ) ))).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         ((v1_relat_1 @ X11)
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.52  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '23'])).
% 0.21/0.52  thf('25', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '5', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t18_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52           ( ( ![E:$i]:
% 0.21/0.52               ( ( r2_hidden @ E @ A ) =>
% 0.21/0.52                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.21/0.52             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X21)
% 0.21/0.52          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.21/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.52          | (r2_relset_1 @ X22 @ X23 @ X24 @ X21)
% 0.21/0.52          | ((k1_funct_1 @ X24 @ (sk_E @ X21 @ X24 @ X22))
% 0.21/0.52              != (k1_funct_1 @ X21 @ (sk_E @ X21 @ X24 @ X22)))
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.52          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.21/0.52          | ~ (v1_funct_1 @ X24))),
% 0.21/0.52      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.52          | (r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.21/0.52          | ~ (v1_funct_1 @ X0))),
% 0.21/0.52      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.21/0.52          | ~ (v1_funct_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_D)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.21/0.52        | (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.52  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('33', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.52  thf('34', plain, ($false), inference('demod', [status(thm)], ['25', '33'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
