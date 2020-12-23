%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H5FPTXjA1t

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:52 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   74 (  99 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  537 (1285 expanded)
%              Number of equality atoms :   35 (  79 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t43_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ! [E: $i] :
            ( ? [F: $i] :
                ( ( E
                  = ( k1_funct_1 @ D @ F ) )
                & ( r2_hidden @ F @ C )
                & ( r2_hidden @ F @ A ) )
           => ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ! [E: $i] :
              ( ? [F: $i] :
                  ( ( E
                    = ( k1_funct_1 @ D @ F ) )
                  & ( r2_hidden @ F @ C )
                  & ( r2_hidden @ F @ A ) )
             => ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    r2_hidden @ sk_F @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ sk_F @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
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

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('12',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','16','19'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X9 )
      | ( X11
       != ( k1_funct_1 @ X9 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( k1_funct_1 @ X9 @ X8 ) ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['6','28'])).

thf('30',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i,X6: $i,X7: $i] :
      ( ( X4
       != ( k9_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X7 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X2 )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['4','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H5FPTXjA1t
% 0.13/0.37  % Computer   : n011.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:19:12 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 115 iterations in 0.171s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.65  thf(t43_funct_2, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.65       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.65         ( ![E:$i]:
% 0.45/0.65           ( ( ?[F:$i]:
% 0.45/0.65               ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & ( r2_hidden @ F @ C ) & 
% 0.45/0.65                 ( r2_hidden @ F @ A ) ) ) =>
% 0.45/0.65             ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.65            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.65          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.65            ( ![E:$i]:
% 0.45/0.65              ( ( ?[F:$i]:
% 0.45/0.65                  ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & 
% 0.45/0.65                    ( r2_hidden @ F @ C ) & ( r2_hidden @ F @ A ) ) ) =>
% 0.45/0.65                ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t43_funct_2])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (~ (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.45/0.65          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.45/0.65           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf('4', plain, (~ (r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.65  thf('5', plain, ((r2_hidden @ sk_F @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('6', plain, ((r2_hidden @ sk_F @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('7', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d1_funct_2, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_1, axiom,
% 0.45/0.65    (![C:$i,B:$i,A:$i]:
% 0.45/0.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.65         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.45/0.65          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.45/0.65          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.45/0.65        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf(zf_stmt_2, axiom,
% 0.45/0.65    (![B:$i,A:$i]:
% 0.45/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X22 : $i, X23 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_5, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.65         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.45/0.65          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.45/0.65          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.45/0.65        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '13'])).
% 0.45/0.65  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('16', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.45/0.65      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.65         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.45/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf('20', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '16', '19'])).
% 0.45/0.65  thf(d4_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65       ( ![B:$i,C:$i]:
% 0.45/0.65         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.45/0.65             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.45/0.65               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.65           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.45/0.65             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.45/0.65               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ X8 @ X11) @ X9)
% 0.45/0.65          | ((X11) != (k1_funct_1 @ X9 @ X8))
% 0.45/0.65          | ~ (v1_funct_1 @ X9)
% 0.45/0.65          | ~ (v1_relat_1 @ X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X9)
% 0.45/0.65          | ~ (v1_funct_1 @ X9)
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ X8 @ (k1_funct_1 @ X9 @ X8)) @ X9)
% 0.45/0.65          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_1 @ X0)) @ sk_D_1)
% 0.45/0.65          | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.65          | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '22'])).
% 0.45/0.65  thf('24', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(cc1_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( v1_relat_1 @ C ) ))).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.65         ((v1_relat_1 @ X12)
% 0.45/0.65          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.65  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_1 @ X0)) @ sk_D_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      ((r2_hidden @ (k4_tarski @ sk_F @ (k1_funct_1 @ sk_D_1 @ sk_F)) @ sk_D_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['6', '28'])).
% 0.45/0.65  thf('30', plain, (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ sk_F))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('31', plain, ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_1)),
% 0.45/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf(d13_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ![B:$i,C:$i]:
% 0.45/0.65         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.45/0.65           ( ![D:$i]:
% 0.45/0.65             ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65               ( ?[E:$i]:
% 0.45/0.65                 ( ( r2_hidden @ E @ B ) & 
% 0.45/0.65                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X1 : $i, X2 : $i, X4 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         (((X4) != (k9_relat_1 @ X2 @ X1))
% 0.45/0.65          | (r2_hidden @ X6 @ X4)
% 0.45/0.65          | ~ (r2_hidden @ (k4_tarski @ X7 @ X6) @ X2)
% 0.45/0.65          | ~ (r2_hidden @ X7 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X1 : $i, X2 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X2)
% 0.45/0.65          | ~ (r2_hidden @ X7 @ X1)
% 0.45/0.65          | ~ (r2_hidden @ (k4_tarski @ X7 @ X6) @ X2)
% 0.45/0.65          | (r2_hidden @ X6 @ (k9_relat_1 @ X2 @ X1)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.45/0.65          | ~ (r2_hidden @ sk_F @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['31', '33'])).
% 0.45/0.65  thf('35', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.45/0.65          | ~ (r2_hidden @ sk_F @ X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf('37', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '36'])).
% 0.45/0.65  thf('38', plain, ($false), inference('demod', [status(thm)], ['4', '37'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
