%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7coyFtkXgc

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:54 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 146 expanded)
%              Number of leaves         :   37 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  608 (1959 expanded)
%              Number of equality atoms :   34 ( 116 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_4 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_4 @ X0 )
      = ( k9_relat_1 @ sk_D_4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    r2_hidden @ sk_F @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ sk_F @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X24 )
       != X22 )
      | ~ ( r2_hidden @ X25 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X25 @ ( sk_E @ X25 @ X24 ) ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_4 ) ) @ sk_D_4 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_4 )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D_4 @ sk_A @ sk_B ),
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

thf('11',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_4 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_4 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D_4 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_4 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    zip_tseitin_1 @ sk_D_4 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_4 ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_4 ) ) @ sk_D_4 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_A != sk_A ) ) ),
    inference(demod,[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_D_4 ) ) @ sk_D_4 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ ( sk_E @ sk_F @ sk_D_4 ) ) @ sk_D_4 ),
    inference('sup-',[status(thm)],['6','22'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k1_relat_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( X17
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ ( k1_funct_1 @ sk_D_4 @ sk_F ) ) @ sk_D_4 )
    | ~ ( v1_funct_1 @ sk_D_4 )
    | ~ ( v1_relat_1 @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( sk_E_1
    = ( k1_funct_1 @ sk_D_4 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_D_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D_4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ sk_E_1 ) @ sk_D_4 ),
    inference(demod,[status(thm)],['29','30','31','36'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_4 )
      | ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_4 ) )
      | ~ ( r2_hidden @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_4 ),
    inference(demod,[status(thm)],['34','35'])).

thf('41',plain,(
    r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_4 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_4 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['4','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7coyFtkXgc
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:41 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.53/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.72  % Solved by: fo/fo7.sh
% 0.53/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.72  % done 103 iterations in 0.233s
% 0.53/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.72  % SZS output start Refutation
% 0.53/0.72  thf(sk_F_type, type, sk_F: $i).
% 0.53/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.72  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.53/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.72  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.53/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.53/0.72  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.53/0.72  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.53/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.53/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.53/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.53/0.72  thf(sk_D_4_type, type, sk_D_4: $i).
% 0.53/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.53/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.53/0.72  thf(t43_funct_2, conjecture,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.72       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.53/0.72         ( ![E:$i]:
% 0.53/0.72           ( ( ?[F:$i]:
% 0.53/0.72               ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & ( r2_hidden @ F @ C ) & 
% 0.53/0.72                 ( r2_hidden @ F @ A ) ) ) =>
% 0.53/0.72             ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.53/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.72            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.72          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.53/0.72            ( ![E:$i]:
% 0.53/0.72              ( ( ?[F:$i]:
% 0.53/0.72                  ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & 
% 0.53/0.72                    ( r2_hidden @ F @ C ) & ( r2_hidden @ F @ A ) ) ) =>
% 0.53/0.72                ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.53/0.72    inference('cnf.neg', [status(esa)], [t43_funct_2])).
% 0.53/0.72  thf('0', plain,
% 0.53/0.72      (~ (r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_4 @ sk_C_1))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('1', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(redefinition_k7_relset_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.72       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.53/0.72  thf('2', plain,
% 0.53/0.72      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.53/0.72          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.53/0.72      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.53/0.72  thf('3', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_4 @ X0)
% 0.53/0.72           = (k9_relat_1 @ sk_D_4 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.72  thf('4', plain, (~ (r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ sk_C_1))),
% 0.53/0.72      inference('demod', [status(thm)], ['0', '3'])).
% 0.53/0.72  thf('5', plain, ((r2_hidden @ sk_F @ sk_C_1)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('6', plain, ((r2_hidden @ sk_F @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('7', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(t22_relset_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.53/0.72       ( ( ![D:$i]:
% 0.53/0.72           ( ~( ( r2_hidden @ D @ B ) & 
% 0.53/0.72                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.53/0.72         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.53/0.72  thf('8', plain,
% 0.53/0.72      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.53/0.72         (((k1_relset_1 @ X22 @ X23 @ X24) != (X22))
% 0.53/0.72          | ~ (r2_hidden @ X25 @ X22)
% 0.53/0.72          | (r2_hidden @ (k4_tarski @ X25 @ (sk_E @ X25 @ X24)) @ X24)
% 0.53/0.72          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.53/0.72      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.53/0.72  thf('9', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_4)) @ sk_D_4)
% 0.53/0.72          | ~ (r2_hidden @ X0 @ sk_A)
% 0.53/0.72          | ((k1_relset_1 @ sk_A @ sk_B @ sk_D_4) != (sk_A)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.72  thf('10', plain, ((v1_funct_2 @ sk_D_4 @ sk_A @ sk_B)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(d1_funct_2, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.53/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.53/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.53/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.53/0.72  thf(zf_stmt_1, axiom,
% 0.53/0.72    (![C:$i,B:$i,A:$i]:
% 0.53/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.53/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.53/0.72  thf('11', plain,
% 0.53/0.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.53/0.72         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.53/0.72          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.53/0.72          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.72  thf('12', plain,
% 0.53/0.72      ((~ (zip_tseitin_1 @ sk_D_4 @ sk_B @ sk_A)
% 0.53/0.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_4)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.53/0.72  thf(zf_stmt_2, axiom,
% 0.53/0.72    (![B:$i,A:$i]:
% 0.53/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.53/0.72  thf('13', plain,
% 0.53/0.72      (![X27 : $i, X28 : $i]:
% 0.53/0.72         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.72  thf('14', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.53/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.53/0.72  thf(zf_stmt_5, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.53/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.53/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.53/0.72  thf('15', plain,
% 0.53/0.72      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.53/0.72         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.53/0.72          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.53/0.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.53/0.72  thf('16', plain,
% 0.53/0.72      (((zip_tseitin_1 @ sk_D_4 @ sk_B @ sk_A)
% 0.53/0.72        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.53/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.72  thf('17', plain,
% 0.53/0.72      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_4 @ sk_B @ sk_A))),
% 0.53/0.72      inference('sup-', [status(thm)], ['13', '16'])).
% 0.53/0.72  thf('18', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('19', plain, ((zip_tseitin_1 @ sk_D_4 @ sk_B @ sk_A)),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.53/0.72  thf('20', plain, (((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_4))),
% 0.53/0.72      inference('demod', [status(thm)], ['12', '19'])).
% 0.53/0.72  thf('21', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_4)) @ sk_D_4)
% 0.53/0.72          | ~ (r2_hidden @ X0 @ sk_A)
% 0.53/0.72          | ((sk_A) != (sk_A)))),
% 0.53/0.72      inference('demod', [status(thm)], ['9', '20'])).
% 0.53/0.72  thf('22', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.53/0.72          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_D_4)) @ sk_D_4))),
% 0.53/0.72      inference('simplify', [status(thm)], ['21'])).
% 0.53/0.72  thf('23', plain,
% 0.53/0.72      ((r2_hidden @ (k4_tarski @ sk_F @ (sk_E @ sk_F @ sk_D_4)) @ sk_D_4)),
% 0.53/0.72      inference('sup-', [status(thm)], ['6', '22'])).
% 0.53/0.72  thf(d4_relat_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.53/0.72       ( ![C:$i]:
% 0.53/0.72         ( ( r2_hidden @ C @ B ) <=>
% 0.53/0.72           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.53/0.72  thf('24', plain,
% 0.53/0.72      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.53/0.72         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X4)
% 0.53/0.72          | (r2_hidden @ X2 @ X5)
% 0.53/0.72          | ((X5) != (k1_relat_1 @ X4)))),
% 0.53/0.72      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.53/0.72  thf('25', plain,
% 0.53/0.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.53/0.72         ((r2_hidden @ X2 @ (k1_relat_1 @ X4))
% 0.53/0.72          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.53/0.72      inference('simplify', [status(thm)], ['24'])).
% 0.53/0.72  thf('26', plain, ((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_4))),
% 0.53/0.72      inference('sup-', [status(thm)], ['23', '25'])).
% 0.53/0.72  thf(t8_funct_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.72       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.53/0.72         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.53/0.72           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.53/0.72  thf('27', plain,
% 0.53/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.53/0.72          | ((X17) != (k1_funct_1 @ X16 @ X15))
% 0.53/0.72          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 0.53/0.72          | ~ (v1_funct_1 @ X16)
% 0.53/0.72          | ~ (v1_relat_1 @ X16))),
% 0.53/0.72      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.53/0.72  thf('28', plain,
% 0.53/0.72      (![X15 : $i, X16 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ X16)
% 0.53/0.72          | ~ (v1_funct_1 @ X16)
% 0.53/0.72          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 0.53/0.72          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['27'])).
% 0.53/0.72  thf('29', plain,
% 0.53/0.72      (((r2_hidden @ (k4_tarski @ sk_F @ (k1_funct_1 @ sk_D_4 @ sk_F)) @ sk_D_4)
% 0.53/0.72        | ~ (v1_funct_1 @ sk_D_4)
% 0.53/0.72        | ~ (v1_relat_1 @ sk_D_4))),
% 0.53/0.72      inference('sup-', [status(thm)], ['26', '28'])).
% 0.53/0.72  thf('30', plain, (((sk_E_1) = (k1_funct_1 @ sk_D_4 @ sk_F))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('31', plain, ((v1_funct_1 @ sk_D_4)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('32', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_D_4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(cc2_relat_1, axiom,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( v1_relat_1 @ A ) =>
% 0.53/0.72       ( ![B:$i]:
% 0.53/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.53/0.72  thf('33', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.53/0.72          | (v1_relat_1 @ X0)
% 0.53/0.72          | ~ (v1_relat_1 @ X1))),
% 0.53/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.72  thf('34', plain,
% 0.53/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_4))),
% 0.53/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.53/0.72  thf(fc6_relat_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.53/0.72  thf('35', plain,
% 0.53/0.72      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.53/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.72  thf('36', plain, ((v1_relat_1 @ sk_D_4)),
% 0.53/0.72      inference('demod', [status(thm)], ['34', '35'])).
% 0.53/0.72  thf('37', plain, ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_1) @ sk_D_4)),
% 0.53/0.72      inference('demod', [status(thm)], ['29', '30', '31', '36'])).
% 0.53/0.72  thf(t143_relat_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( v1_relat_1 @ C ) =>
% 0.53/0.72       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.53/0.72         ( ?[D:$i]:
% 0.53/0.72           ( ( r2_hidden @ D @ B ) & 
% 0.53/0.72             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.53/0.72             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.53/0.72  thf('38', plain,
% 0.53/0.72      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X11 @ X12)
% 0.53/0.72          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ X14)
% 0.53/0.72          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X14))
% 0.53/0.72          | (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.53/0.72          | ~ (v1_relat_1 @ X14))),
% 0.53/0.72      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.53/0.72  thf('39', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (v1_relat_1 @ sk_D_4)
% 0.53/0.72          | (r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ X0))
% 0.53/0.72          | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_4))
% 0.53/0.72          | ~ (r2_hidden @ sk_F @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.53/0.72  thf('40', plain, ((v1_relat_1 @ sk_D_4)),
% 0.53/0.72      inference('demod', [status(thm)], ['34', '35'])).
% 0.53/0.72  thf('41', plain, ((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_4))),
% 0.53/0.72      inference('sup-', [status(thm)], ['23', '25'])).
% 0.53/0.72  thf('42', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ X0))
% 0.53/0.72          | ~ (r2_hidden @ sk_F @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.53/0.72  thf('43', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_4 @ sk_C_1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['5', '42'])).
% 0.53/0.72  thf('44', plain, ($false), inference('demod', [status(thm)], ['4', '43'])).
% 0.53/0.72  
% 0.53/0.72  % SZS output end Refutation
% 0.53/0.72  
% 0.53/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
