%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A0SHck7zMZ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 108 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  443 (1351 expanded)
%              Number of equality atoms :   41 ( 106 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ( X11
        = ( k1_relset_1 @ X11 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('9',plain,(
    ! [X9: $i] :
      ( zip_tseitin_0 @ X9 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('24',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D = X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_D = sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_D = sk_C_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A0SHck7zMZ
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:13:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 41 iterations in 0.045s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.19/0.50  thf(t85_funct_2, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.50       ( ( v2_funct_1 @ B ) =>
% 0.19/0.50         ( ![C:$i,D:$i]:
% 0.19/0.50           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.19/0.50               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.19/0.50             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.50          ( ( v2_funct_1 @ B ) =>
% 0.19/0.50            ( ![C:$i,D:$i]:
% 0.19/0.50              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.19/0.50                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.19/0.50                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d1_funct_2, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.50           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.19/0.50             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.50           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.19/0.50             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_1, axiom,
% 0.19/0.50    (![C:$i,B:$i,A:$i]:
% 0.19/0.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.19/0.50       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         (~ (v1_funct_2 @ X13 @ X11 @ X12)
% 0.19/0.50          | ((X11) = (k1_relset_1 @ X11 @ X12 @ X13))
% 0.19/0.50          | ~ (zip_tseitin_1 @ X13 @ X12 @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      ((~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)
% 0.19/0.50        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B_1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.19/0.50  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.19/0.50  thf(zf_stmt_4, axiom,
% 0.19/0.50    (![B:$i,A:$i]:
% 0.19/0.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.50       ( zip_tseitin_0 @ B @ A ) ))).
% 0.19/0.50  thf(zf_stmt_5, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.19/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.50         (~ (zip_tseitin_0 @ X14 @ X15)
% 0.19/0.50          | (zip_tseitin_1 @ X16 @ X14 @ X15)
% 0.19/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)
% 0.19/0.50        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ X9 @ X10) | ((X10) != (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.19/0.50  thf('9', plain, (![X9 : $i]: (zip_tseitin_0 @ X9 @ k1_xboole_0)),
% 0.19/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.19/0.50      inference('sup+', [status(thm)], ['7', '9'])).
% 0.19/0.50  thf('11', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.19/0.50      inference('eq_fact', [status(thm)], ['10'])).
% 0.19/0.50  thf('12', plain, ((zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['6', '11'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.19/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.19/0.50  thf(d8_funct_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.50       ( ( v2_funct_1 @ A ) <=>
% 0.19/0.50         ( ![B:$i,C:$i]:
% 0.19/0.50           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.50               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.50               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.19/0.50             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (v2_funct_1 @ X0)
% 0.19/0.50          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.19/0.50          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.19/0.50          | ((k1_funct_1 @ X0 @ X1) != (k1_funct_1 @ X0 @ X2))
% 0.19/0.50          | ((X1) = (X2))
% 0.19/0.50          | ~ (v1_funct_1 @ X0)
% 0.19/0.50          | ~ (v1_relat_1 @ X0))),
% 0.19/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.50          | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.50          | ((X0) = (X1))
% 0.19/0.50          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.19/0.50          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.19/0.50          | ~ (v2_funct_1 @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc1_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( v1_relat_1 @ C ) ))).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((v1_relat_1 @ X3)
% 0.19/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.50  thf('21', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.50  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('23', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.19/0.50  thf('24', plain, ((v2_funct_1 @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.50          | ((X0) = (X1))
% 0.19/0.50          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.19/0.50          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['18', '21', '22', '23', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.50          | ((sk_D) = (X0))
% 0.19/0.50          | ~ (r2_hidden @ sk_D @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '25'])).
% 0.19/0.50  thf('27', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.50          | ((sk_D) = (X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain, ((((sk_D) = (sk_C_1)) | ~ (r2_hidden @ sk_C_1 @ sk_A))),
% 0.19/0.50      inference('eq_res', [status(thm)], ['28'])).
% 0.19/0.50  thf('30', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('31', plain, (((sk_D) = (sk_C_1))),
% 0.19/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain, (((sk_C_1) != (sk_D))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('33', plain, ($false),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
