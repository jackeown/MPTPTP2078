%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.imzTTRGZ4s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 137 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  418 (1508 expanded)
%              Number of equality atoms :   23 (  65 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2
        = ( k7_relat_1 @ X2 @ X3 ) )
      | ~ ( v4_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k9_relat_1 @ sk_D_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k9_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k9_relat_1 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X14 @ X10 @ X11 ) @ X14 @ X10 @ X11 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X14 @ X10 @ X11 ) @ X14 @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_A @ sk_D_1 ) @ X0 @ sk_A @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_A @ sk_D_1 ) @ X0 @ sk_A @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) @ sk_C @ sk_A @ sk_D_1 ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ X7 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    r2_hidden @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X26 )
       != sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) )
 != sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) @ sk_C @ sk_A @ sk_D_1 ),
    inference('sup-',[status(thm)],['4','23'])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
        = ( k1_funct_1 @ X4 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,
    ( sk_C
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.imzTTRGZ4s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 28 iterations in 0.016s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.20/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.46  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.46  thf(t17_funct_2, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.46            ( ![E:$i]:
% 0.20/0.46              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.46            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.46               ( ![E:$i]:
% 0.20/0.46                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.20/0.46                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.20/0.46  thf('0', plain, ((r2_hidden @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.46         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.20/0.46          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc2_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.46         ((v4_relat_1 @ X20 @ X21)
% 0.20/0.46          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.46  thf('7', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf(t209_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.46       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]:
% 0.20/0.46         (((X2) = (k7_relat_1 @ X2 @ X3))
% 0.20/0.46          | ~ (v4_relat_1 @ X2 @ X3)
% 0.20/0.46          | ~ (v1_relat_1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ sk_D_1) | ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc1_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( v1_relat_1 @ C ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.46         ((v1_relat_1 @ X17)
% 0.20/0.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.46  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain, (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '12'])).
% 0.20/0.46  thf(t148_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) = (k9_relat_1 @ X0 @ X1))
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ sk_A))
% 0.20/0.46        | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('17', plain, (((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf(d12_funct_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.46       ( ![B:$i,C:$i]:
% 0.20/0.46         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.46           ( ![D:$i]:
% 0.20/0.46             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.46               ( ?[E:$i]:
% 0.20/0.46                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.46                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.46  thf(zf_stmt_2, axiom,
% 0.20/0.46    (![E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.46     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.20/0.46       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.20/0.46         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_3, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.46       ( ![B:$i,C:$i]:
% 0.20/0.46         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.46           ( ![D:$i]:
% 0.20/0.46             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.46               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.46         (((X13) != (k9_relat_1 @ X11 @ X10))
% 0.20/0.46          | (zip_tseitin_0 @ (sk_E_1 @ X14 @ X10 @ X11) @ X14 @ X10 @ X11)
% 0.20/0.46          | ~ (r2_hidden @ X14 @ X13)
% 0.20/0.46          | ~ (v1_funct_1 @ X11)
% 0.20/0.46          | ~ (v1_relat_1 @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i, X14 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X11)
% 0.20/0.46          | ~ (v1_funct_1 @ X11)
% 0.20/0.46          | ~ (r2_hidden @ X14 @ (k9_relat_1 @ X11 @ X10))
% 0.20/0.46          | (zip_tseitin_0 @ (sk_E_1 @ X14 @ X10 @ X11) @ X14 @ X10 @ X11))),
% 0.20/0.46      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.20/0.46          | (zip_tseitin_0 @ (sk_E_1 @ X0 @ sk_A @ sk_D_1) @ X0 @ sk_A @ sk_D_1)
% 0.20/0.46          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.46          | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.46  thf('21', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.20/0.46          | (zip_tseitin_0 @ (sk_E_1 @ X0 @ sk_A @ sk_D_1) @ X0 @ sk_A @ sk_D_1))),
% 0.20/0.46      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1) @ sk_C @ sk_A @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '23'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((r2_hidden @ X5 @ X7) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.46  thf('26', plain, ((r2_hidden @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1) @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X26 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X26 @ sk_A) | ((k1_funct_1 @ sk_D_1 @ X26) != (sk_C)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (((k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1)) != (sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1) @ sk_C @ sk_A @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '23'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         (((X6) = (k1_funct_1 @ X4 @ X5))
% 0.20/0.46          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (((sk_C) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain, (((sk_C) != (sk_C))),
% 0.20/0.46      inference('demod', [status(thm)], ['28', '31'])).
% 0.20/0.46  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
