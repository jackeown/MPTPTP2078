%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5DthVfDX3X

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:59 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   64 (  80 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  443 ( 811 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('3',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('11',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( X26
       != ( k1_funct_1 @ X25 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ ( k1_funct_1 @ X25 @ X24 ) ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D @ X0 ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) ) @ sk_D ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5DthVfDX3X
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.82  % Solved by: fo/fo7.sh
% 0.61/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.82  % done 325 iterations in 0.358s
% 0.61/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.82  % SZS output start Refutation
% 0.61/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.82  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.82  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.61/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.61/0.82  thf(sk_D_type, type, sk_D: $i).
% 0.61/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.61/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.61/0.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.61/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.82  thf(t7_funct_2, conjecture,
% 0.61/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.82     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.61/0.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.82       ( ( r2_hidden @ C @ A ) =>
% 0.61/0.82         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.61/0.82           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.61/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.82    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.82        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.61/0.82            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.82          ( ( r2_hidden @ C @ A ) =>
% 0.61/0.82            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.61/0.82              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.61/0.82    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.61/0.82  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ sk_B_1)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('2', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(d1_funct_2, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.61/0.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.61/0.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.61/0.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.61/0.82  thf(zf_stmt_1, axiom,
% 0.61/0.82    (![C:$i,B:$i,A:$i]:
% 0.61/0.82     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.61/0.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.61/0.82  thf('3', plain,
% 0.61/0.82      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.61/0.82         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.61/0.82          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.61/0.82          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.82  thf('4', plain,
% 0.61/0.82      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.61/0.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.61/0.82  thf('5', plain,
% 0.61/0.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.82  thf('6', plain,
% 0.61/0.82      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.61/0.82         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.61/0.82          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.61/0.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.82  thf('7', plain,
% 0.61/0.82      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.61/0.82      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.82  thf('8', plain,
% 0.61/0.82      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.61/0.82        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.61/0.82      inference('demod', [status(thm)], ['4', '7'])).
% 0.61/0.82  thf(zf_stmt_2, axiom,
% 0.61/0.82    (![B:$i,A:$i]:
% 0.61/0.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.82       ( zip_tseitin_0 @ B @ A ) ))).
% 0.61/0.82  thf('9', plain,
% 0.61/0.82      (![X38 : $i, X39 : $i]:
% 0.61/0.82         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.82  thf('10', plain,
% 0.61/0.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.61/0.82  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.61/0.82  thf(zf_stmt_5, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.82       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.61/0.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.61/0.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.61/0.82  thf('11', plain,
% 0.61/0.82      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.61/0.82         (~ (zip_tseitin_0 @ X43 @ X44)
% 0.61/0.82          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 0.61/0.82          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.61/0.82  thf('12', plain,
% 0.61/0.82      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.61/0.82        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['10', '11'])).
% 0.61/0.82  thf('13', plain,
% 0.61/0.82      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['9', '12'])).
% 0.61/0.82  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('15', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.61/0.82      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.61/0.82  thf('16', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.61/0.82      inference('demod', [status(thm)], ['8', '15'])).
% 0.61/0.82  thf(t8_funct_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.61/0.82       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.61/0.82         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.61/0.82           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.61/0.82  thf('17', plain,
% 0.61/0.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.61/0.82          | ((X26) != (k1_funct_1 @ X25 @ X24))
% 0.61/0.82          | (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.61/0.82          | ~ (v1_funct_1 @ X25)
% 0.61/0.82          | ~ (v1_relat_1 @ X25))),
% 0.61/0.82      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.61/0.82  thf('18', plain,
% 0.61/0.82      (![X24 : $i, X25 : $i]:
% 0.61/0.82         (~ (v1_relat_1 @ X25)
% 0.61/0.82          | ~ (v1_funct_1 @ X25)
% 0.61/0.82          | (r2_hidden @ (k4_tarski @ X24 @ (k1_funct_1 @ X25 @ X24)) @ X25)
% 0.61/0.82          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X25)))),
% 0.61/0.82      inference('simplify', [status(thm)], ['17'])).
% 0.61/0.82  thf('19', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.82          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D)
% 0.61/0.82          | ~ (v1_funct_1 @ sk_D)
% 0.61/0.82          | ~ (v1_relat_1 @ sk_D))),
% 0.61/0.82      inference('sup-', [status(thm)], ['16', '18'])).
% 0.61/0.82  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('21', plain,
% 0.61/0.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(cc1_relset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.82       ( v1_relat_1 @ C ) ))).
% 0.61/0.82  thf('22', plain,
% 0.61/0.82      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.61/0.82         ((v1_relat_1 @ X27)
% 0.61/0.82          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.61/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.61/0.82  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.61/0.82      inference('sup-', [status(thm)], ['21', '22'])).
% 0.61/0.82  thf('24', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.82          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D @ X0)) @ sk_D))),
% 0.61/0.82      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.61/0.82  thf('25', plain,
% 0.61/0.82      ((r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D @ sk_C_1)) @ sk_D)),
% 0.61/0.82      inference('sup-', [status(thm)], ['1', '24'])).
% 0.61/0.82  thf('26', plain,
% 0.61/0.82      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(l3_subset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.61/0.82  thf('27', plain,
% 0.61/0.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X15 @ X16)
% 0.61/0.82          | (r2_hidden @ X15 @ X17)
% 0.61/0.82          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.61/0.82      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.61/0.82  thf('28', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.61/0.82          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.61/0.82      inference('sup-', [status(thm)], ['26', '27'])).
% 0.61/0.82  thf('29', plain,
% 0.61/0.82      ((r2_hidden @ (k4_tarski @ sk_C_1 @ (k1_funct_1 @ sk_D @ sk_C_1)) @ 
% 0.61/0.82        (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.61/0.82      inference('sup-', [status(thm)], ['25', '28'])).
% 0.61/0.82  thf(l54_zfmisc_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.82     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.61/0.82       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.61/0.82  thf('30', plain,
% 0.61/0.82      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.61/0.82         ((r2_hidden @ X9 @ X10)
% 0.61/0.82          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.61/0.82      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.61/0.82  thf('31', plain, ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ sk_B_1)),
% 0.61/0.82      inference('sup-', [status(thm)], ['29', '30'])).
% 0.61/0.82  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.61/0.82  
% 0.61/0.82  % SZS output end Refutation
% 0.61/0.82  
% 0.61/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
