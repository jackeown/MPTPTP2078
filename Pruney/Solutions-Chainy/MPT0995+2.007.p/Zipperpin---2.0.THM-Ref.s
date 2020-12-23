%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sh4Yg3aLpA

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:53 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   76 (  96 expanded)
%              Number of leaves         :   37 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  541 (1201 expanded)
%              Number of equality atoms :   35 (  75 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_F @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_F @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_2 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_1 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_1 @ X29 @ X30 )
      | ( zip_tseitin_2 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','15','18'])).

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

thf(zf_stmt_6,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ( X6
       != ( k1_funct_1 @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('21',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X8 ) )
      | ( zip_tseitin_0 @ X5 @ ( k1_funct_1 @ X8 @ X5 ) @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_F @ X0 )
      | ( zip_tseitin_0 @ sk_F @ ( k1_funct_1 @ sk_D_1 @ sk_F ) @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_F @ X0 )
      | ( zip_tseitin_0 @ sk_F @ sk_E_2 @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    zip_tseitin_0 @ sk_F @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference('sup-',[status(thm)],['4','25'])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
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

thf('27',plain,(
    ! [X10: $i,X11: $i,X13: $i,X15: $i,X16: $i] :
      ( ( X13
       != ( k9_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X15 @ X13 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X10 @ X11 )
      | ( r2_hidden @ X15 @ ( k9_relat_1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','3','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sh4Yg3aLpA
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 15:15:54 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 83 iterations in 0.119s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.57  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.38/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.57  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(t43_funct_2, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.57         ( ![E:$i]:
% 0.38/0.57           ( ( ?[F:$i]:
% 0.38/0.57               ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & ( r2_hidden @ F @ C ) & 
% 0.38/0.57                 ( r2_hidden @ F @ A ) ) ) =>
% 0.38/0.57             ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.57            ( ![E:$i]:
% 0.38/0.57              ( ( ?[F:$i]:
% 0.38/0.57                  ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & 
% 0.38/0.57                    ( r2_hidden @ F @ C ) & ( r2_hidden @ F @ A ) ) ) =>
% 0.38/0.57                ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t43_funct_2])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (~ (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.38/0.57          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.38/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf('4', plain, ((r2_hidden @ sk_F @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('5', plain, ((r2_hidden @ sk_F @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d1_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_1, axiom,
% 0.38/0.57    (![C:$i,B:$i,A:$i]:
% 0.38/0.57     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.38/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.57         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.38/0.57          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.38/0.57          | ~ (zip_tseitin_2 @ X28 @ X27 @ X26))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.38/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf(zf_stmt_2, axiom,
% 0.38/0.57    (![B:$i,A:$i]:
% 0.38/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.57       ( zip_tseitin_1 @ B @ A ) ))).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X24 : $i, X25 : $i]:
% 0.38/0.57         ((zip_tseitin_1 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_5, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.38/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.57         (~ (zip_tseitin_1 @ X29 @ X30)
% 0.38/0.57          | (zip_tseitin_2 @ X31 @ X29 @ X30)
% 0.38/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.38/0.57        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['9', '12'])).
% 0.38/0.57  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('15', plain, ((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.57         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.38/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.57  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.38/0.57      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.38/0.57  thf(d12_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.38/0.57       ( ![B:$i,C:$i]:
% 0.38/0.57         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.38/0.57           ( ![D:$i]:
% 0.38/0.57             ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.57               ( ?[E:$i]:
% 0.38/0.57                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.57                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_6, axiom,
% 0.38/0.57    (![E:$i,D:$i,B:$i,A:$i]:
% 0.38/0.57     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.38/0.57       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.38/0.57         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.57         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.38/0.57          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X8))
% 0.38/0.57          | ~ (r2_hidden @ X5 @ X7)
% 0.38/0.57          | ((X6) != (k1_funct_1 @ X8 @ X5)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X5 @ X7)
% 0.38/0.57          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X8))
% 0.38/0.57          | (zip_tseitin_0 @ X5 @ (k1_funct_1 @ X8 @ X5) @ X7 @ X8))),
% 0.38/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.57          | (zip_tseitin_0 @ X0 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1 @ sk_D_1)
% 0.38/0.57          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r2_hidden @ sk_F @ X0)
% 0.38/0.57          | (zip_tseitin_0 @ sk_F @ (k1_funct_1 @ sk_D_1 @ sk_F) @ X0 @ sk_D_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '22'])).
% 0.38/0.57  thf('24', plain, (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ sk_F))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r2_hidden @ sk_F @ X0)
% 0.38/0.57          | (zip_tseitin_0 @ sk_F @ sk_E_2 @ X0 @ sk_D_1))),
% 0.38/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.57  thf('26', plain, ((zip_tseitin_0 @ sk_F @ sk_E_2 @ sk_C @ sk_D_1)),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '25'])).
% 0.38/0.57  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_8, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ![B:$i,C:$i]:
% 0.38/0.57         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.38/0.57           ( ![D:$i]:
% 0.38/0.57             ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.57               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (((X13) != (k9_relat_1 @ X11 @ X10))
% 0.38/0.57          | (r2_hidden @ X15 @ X13)
% 0.38/0.57          | ~ (zip_tseitin_0 @ X16 @ X15 @ X10 @ X11)
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X11)
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (zip_tseitin_0 @ X16 @ X15 @ X10 @ X11)
% 0.38/0.57          | (r2_hidden @ X15 @ (k9_relat_1 @ X11 @ X10)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))
% 0.38/0.57        | ~ (v1_funct_1 @ sk_D_1)
% 0.38/0.57        | ~ (v1_relat_1 @ sk_D_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['26', '28'])).
% 0.38/0.57  thf('30', plain, ((v1_funct_1 @ sk_D_1)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc2_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.38/0.57          | (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.57  thf(fc6_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.57  thf('35', plain, ((v1_relat_1 @ sk_D_1)),
% 0.38/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.38/0.57  thf('36', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['29', '30', '35'])).
% 0.38/0.57  thf('37', plain, ($false),
% 0.38/0.57      inference('demod', [status(thm)], ['0', '3', '36'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
