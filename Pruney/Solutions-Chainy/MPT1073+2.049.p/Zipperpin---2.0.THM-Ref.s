%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e6Am7mXKZf

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  404 (1169 expanded)
%              Number of equality atoms :   19 (  50 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k7_relset_1 @ X23 @ X24 @ X25 @ X23 )
        = ( k2_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('3',plain,
    ( ( k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k9_relat_1 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X16 @ X12 @ X13 ) @ X16 @ X12 @ X13 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X16 @ X12 @ X13 ) @ X16 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_A @ sk_B @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_A @ sk_B @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8
        = ( k1_funct_1 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_A @ sk_B @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12','17'])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ X9 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X26: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e6Am7mXKZf
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:42:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 41 iterations in 0.044s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.22/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.55  thf(t190_funct_2, conjecture,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.22/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.22/0.55       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.22/0.55            ( ![E:$i]:
% 0.22/0.55              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.22/0.55            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.22/0.55          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.22/0.55               ( ![E:$i]:
% 0.22/0.55                 ( ( m1_subset_1 @ E @ B ) =>
% 0.22/0.55                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.22/0.55  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t38_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.55         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.55         (((k7_relset_1 @ X23 @ X24 @ X25 @ X23)
% 0.22/0.55            = (k2_relset_1 @ X23 @ X24 @ X25))
% 0.22/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.22/0.55      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (((k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ sk_B)
% 0.22/0.55         = (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.55       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.22/0.55          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k7_relset_1 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.22/0.55           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (((k9_relat_1 @ sk_D_1 @ sk_B) = (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.22/0.55      inference('demod', [status(thm)], ['3', '6'])).
% 0.22/0.55  thf('8', plain, ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.55  thf(d12_funct_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.22/0.55       ( ![B:$i,C:$i]:
% 0.22/0.55         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.22/0.55           ( ![D:$i]:
% 0.22/0.55             ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.55               ( ?[E:$i]:
% 0.22/0.55                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.55                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.55  thf(zf_stmt_2, axiom,
% 0.22/0.55    (![E:$i,D:$i,B:$i,A:$i]:
% 0.22/0.55     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.22/0.55       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.22/0.55         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_3, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.55       ( ![B:$i,C:$i]:
% 0.22/0.55         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.22/0.55           ( ![D:$i]:
% 0.22/0.55             ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.55               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.22/0.55         (((X15) != (k9_relat_1 @ X13 @ X12))
% 0.22/0.55          | (zip_tseitin_0 @ (sk_E_1 @ X16 @ X12 @ X13) @ X16 @ X12 @ X13)
% 0.22/0.55          | ~ (r2_hidden @ X16 @ X15)
% 0.22/0.55          | ~ (v1_funct_1 @ X13)
% 0.22/0.55          | ~ (v1_relat_1 @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X13)
% 0.22/0.55          | ~ (v1_funct_1 @ X13)
% 0.22/0.55          | ~ (r2_hidden @ X16 @ (k9_relat_1 @ X13 @ X12))
% 0.22/0.55          | (zip_tseitin_0 @ (sk_E_1 @ X16 @ X12 @ X13) @ X16 @ X12 @ X13))),
% 0.22/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (((zip_tseitin_0 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_A @ sk_B @ sk_D_1)
% 0.22/0.55        | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.55        | ~ (v1_relat_1 @ sk_D_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.55  thf('12', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(cc2_relat_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X2 : $i, X3 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.22/0.55          | (v1_relat_1 @ X2)
% 0.22/0.55          | ~ (v1_relat_1 @ X3))),
% 0.22/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.55  thf(fc6_relat_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.55  thf('17', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      ((zip_tseitin_0 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_A @ sk_B @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['11', '12', '17'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.55         (((X8) = (k1_funct_1 @ X6 @ X7))
% 0.22/0.55          | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      ((zip_tseitin_0 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_A @ sk_B @ sk_D_1)),
% 0.22/0.55      inference('demod', [status(thm)], ['11', '12', '17'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.55         ((r2_hidden @ X7 @ X9) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.55  thf('23', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.55  thf(t1_subset, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.55  thf('25', plain, ((m1_subset_1 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1) @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      (![X26 : $i]:
% 0.22/0.55         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X26))
% 0.22/0.55          | ~ (m1_subset_1 @ X26 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf('28', plain, ($false),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['20', '27'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
