%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5csVcYsCZy

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 105 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  551 (1313 expanded)
%              Number of equality atoms :   35 (  79 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X15 ) @ X13 )
      | ( X15
       != ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( k1_funct_1 @ X13 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['23','24','29'])).

thf('31',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['6','30'])).

thf('32',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

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

thf('34',plain,(
    ! [X3: $i,X4: $i,X6: $i,X8: $i,X9: $i] :
      ( ( X6
       != ( k9_relat_1 @ X4 @ X3 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X8 ) @ X4 )
      | ~ ( r2_hidden @ X9 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ X9 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X8 ) @ X4 )
      | ( r2_hidden @ X8 @ ( k9_relat_1 @ X4 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['27','28'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['4','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5csVcYsCZy
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 103 iterations in 0.114s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.20/0.56  thf(t43_funct_2, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.56         ( ![E:$i]:
% 0.20/0.56           ( ( ?[F:$i]:
% 0.20/0.56               ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.56                 ( r2_hidden @ F @ A ) ) ) =>
% 0.20/0.56             ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.56          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.56            ( ![E:$i]:
% 0.20/0.56              ( ( ?[F:$i]:
% 0.20/0.56                  ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & 
% 0.20/0.56                    ( r2_hidden @ F @ C ) & ( r2_hidden @ F @ A ) ) ) =>
% 0.20/0.56                ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t43_funct_2])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (~ (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.56          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.20/0.56           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('4', plain, (~ (r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.56  thf('5', plain, ((r2_hidden @ sk_F @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('6', plain, ((r2_hidden @ sk_F @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('7', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d1_funct_2, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_1, axiom,
% 0.20/0.56    (![C:$i,B:$i,A:$i]:
% 0.20/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.56         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.20/0.56          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.20/0.56          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.20/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf(zf_stmt_2, axiom,
% 0.20/0.56    (![B:$i,A:$i]:
% 0.20/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X23 : $i, X24 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_5, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.56         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.20/0.56          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.20/0.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.20/0.56        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.56  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('16', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.56         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.20/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.56  thf('20', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '16', '19'])).
% 0.20/0.56  thf(d4_funct_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.56       ( ![B:$i,C:$i]:
% 0.20/0.56         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.56               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.56           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.56               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X12 @ X15) @ X13)
% 0.20/0.56          | ((X15) != (k1_funct_1 @ X13 @ X12))
% 0.20/0.56          | ~ (v1_funct_1 @ X13)
% 0.20/0.56          | ~ (v1_relat_1 @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X12 : $i, X13 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X13)
% 0.20/0.56          | ~ (v1_funct_1 @ X13)
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X12 @ (k1_funct_1 @ X13 @ X12)) @ X13)
% 0.20/0.56          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_1 @ X0)) @ sk_D_1)
% 0.20/0.56          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.56          | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.56  thf('24', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc2_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.56          | (v1_relat_1 @ X0)
% 0.20/0.56          | ~ (v1_relat_1 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf(fc6_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.56  thf('29', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_1 @ X0)) @ sk_D_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['23', '24', '29'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      ((r2_hidden @ (k4_tarski @ sk_F @ (k1_funct_1 @ sk_D_1 @ sk_F)) @ sk_D_1)),
% 0.20/0.56      inference('sup-', [status(thm)], ['6', '30'])).
% 0.20/0.56  thf('32', plain, (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ sk_F))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('33', plain, ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.56  thf(d13_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ![B:$i,C:$i]:
% 0.20/0.56         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.56           ( ![D:$i]:
% 0.20/0.56             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.56               ( ?[E:$i]:
% 0.20/0.56                 ( ( r2_hidden @ E @ B ) & 
% 0.20/0.56                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X3 : $i, X4 : $i, X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.56         (((X6) != (k9_relat_1 @ X4 @ X3))
% 0.20/0.56          | (r2_hidden @ X8 @ X6)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X9 @ X8) @ X4)
% 0.20/0.56          | ~ (r2_hidden @ X9 @ X3)
% 0.20/0.56          | ~ (v1_relat_1 @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X3 : $i, X4 : $i, X8 : $i, X9 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X4)
% 0.20/0.56          | ~ (r2_hidden @ X9 @ X3)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X9 @ X8) @ X4)
% 0.20/0.56          | (r2_hidden @ X8 @ (k9_relat_1 @ X4 @ X3)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.20/0.56          | ~ (r2_hidden @ sk_F @ X0)
% 0.20/0.56          | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.56  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.20/0.56          | ~ (r2_hidden @ sk_F @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '38'])).
% 0.20/0.56  thf('40', plain, ($false), inference('demod', [status(thm)], ['4', '39'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
