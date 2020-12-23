%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gNgttjLGT6

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  80 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  453 (1047 expanded)
%              Number of equality atoms :   33 (  69 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t21_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_relat_1 @ E )
            & ( v1_funct_1 @ E ) )
         => ( ( r2_hidden @ C @ A )
           => ( ( B = k1_xboole_0 )
              | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E ) )
           => ( ( r2_hidden @ C @ A )
             => ( ( B = k1_xboole_0 )
                | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                  = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ( X12
        = ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k1_funct_1 @ X4 @ ( k1_funct_1 @ X5 @ X6 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_C )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_C ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_C ) )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gNgttjLGT6
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 59 iterations in 0.085s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.57  thf(t21_funct_2, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ![E:$i]:
% 0.21/0.57         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.21/0.57           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.57             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.21/0.57                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57          ( ![E:$i]:
% 0.21/0.57            ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.21/0.57              ( ( r2_hidden @ C @ A ) =>
% 0.21/0.57                ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57                  ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.21/0.57                    ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t21_funct_2])).
% 0.21/0.57  thf('0', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d1_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_1, axiom,
% 0.21/0.57    (![C:$i,B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.21/0.57          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 0.21/0.57          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.21/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(zf_stmt_2, axiom,
% 0.21/0.57    (![B:$i,A:$i]:
% 0.21/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_5, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (zip_tseitin_0 @ X15 @ X16)
% 0.21/0.57          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 0.21/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.57  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.21/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.57  thf('14', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.21/0.57  thf(t23_funct_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.57             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.57               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X4)
% 0.21/0.57          | ~ (v1_funct_1 @ X4)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 0.21/0.57              = (k1_funct_1 @ X4 @ (k1_funct_1 @ X5 @ X6)))
% 0.21/0.57          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X5))
% 0.21/0.57          | ~ (v1_funct_1 @ X5)
% 0.21/0.57          | ~ (v1_relat_1 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.57          | ~ (v1_relat_1 @ sk_D)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.21/0.57              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.57          | ~ (v1_funct_1 @ X1)
% 0.21/0.57          | ~ (v1_relat_1 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc2_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.57          | (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.57  thf(fc6_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.57  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.57  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.21/0.57              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.57          | ~ (v1_funct_1 @ X1)
% 0.21/0.57          | ~ (v1_relat_1 @ X1))),
% 0.21/0.57      inference('demod', [status(thm)], ['16', '21', '22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_C)
% 0.21/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_C))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_C)
% 0.21/0.57         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_C))
% 0.21/0.57          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_C)))
% 0.21/0.57        | ~ (v1_funct_1 @ sk_E)
% 0.21/0.57        | ~ (v1_relat_1 @ sk_E))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('28', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_C))
% 0.21/0.57         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_C)))),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.57  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
