%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tq1QcsBcFv

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:54 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 132 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  532 (1786 expanded)
%              Number of equality atoms :   32 ( 110 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k7_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k9_relat_1 @ X14 @ X17 ) ) ) ),
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
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( X10
       != ( k1_funct_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( k1_funct_1 @ X9 @ X8 ) ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('36',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('37',plain,(
    r2_hidden @ sk_F @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','3','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tq1QcsBcFv
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:15:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 99 iterations in 0.079s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.35/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.54  thf(t43_funct_2, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.54         ( ![E:$i]:
% 0.35/0.54           ( ( ?[F:$i]:
% 0.35/0.54               ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & ( r2_hidden @ F @ C ) & 
% 0.35/0.54                 ( r2_hidden @ F @ A ) ) ) =>
% 0.35/0.54             ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.54            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.54            ( ![E:$i]:
% 0.35/0.54              ( ( ?[F:$i]:
% 0.35/0.54                  ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & 
% 0.35/0.54                    ( r2_hidden @ F @ C ) & ( r2_hidden @ F @ A ) ) ) =>
% 0.35/0.54                ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t43_funct_2])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.35/0.54          | ((k7_relset_1 @ X15 @ X16 @ X14 @ X17) = (k9_relat_1 @ X14 @ X17)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.35/0.54           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.54  thf('4', plain, ((r2_hidden @ sk_F @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('5', plain, ((r2_hidden @ sk_F @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(d1_funct_2, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_1, axiom,
% 0.35/0.54    (![C:$i,B:$i,A:$i]:
% 0.35/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.35/0.54         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.35/0.54          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.35/0.54          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.35/0.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.54  thf(zf_stmt_2, axiom,
% 0.35/0.54    (![B:$i,A:$i]:
% 0.35/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i]:
% 0.35/0.54         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.54  thf(zf_stmt_5, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.35/0.54         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.35/0.54          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.35/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.35/0.54        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['9', '12'])).
% 0.35/0.54  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('15', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.54         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.35/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.54  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.35/0.54  thf(t8_funct_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.35/0.54         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.35/0.54           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.35/0.54          | ((X10) != (k1_funct_1 @ X9 @ X8))
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X8 @ X10) @ X9)
% 0.35/0.54          | ~ (v1_funct_1 @ X9)
% 0.35/0.54          | ~ (v1_relat_1 @ X9))),
% 0.35/0.54      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X9)
% 0.35/0.54          | ~ (v1_funct_1 @ X9)
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X8 @ (k1_funct_1 @ X9 @ X8)) @ X9)
% 0.35/0.54          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X9)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_1 @ X0)) @ sk_D_1)
% 0.35/0.54          | ~ (v1_funct_1 @ sk_D_1)
% 0.35/0.54          | ~ (v1_relat_1 @ sk_D_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['19', '21'])).
% 0.35/0.54  thf('23', plain, ((v1_funct_1 @ sk_D_1)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc2_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.35/0.54          | (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (v1_relat_1 @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.35/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.54  thf(fc6_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.54  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.35/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.54          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_1 @ X0)) @ sk_D_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['22', '23', '28'])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      ((r2_hidden @ (k4_tarski @ sk_F @ (k1_funct_1 @ sk_D_1 @ sk_F)) @ sk_D_1)),
% 0.35/0.54      inference('sup-', [status(thm)], ['5', '29'])).
% 0.35/0.54  thf('31', plain, (((sk_E) = (k1_funct_1 @ sk_D_1 @ sk_F))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('32', plain, ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)),
% 0.35/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.35/0.54  thf(t143_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ C ) =>
% 0.35/0.54       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.35/0.54         ( ?[D:$i]:
% 0.35/0.54           ( ( r2_hidden @ D @ B ) & 
% 0.35/0.54             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.35/0.54             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X4 @ X5)
% 0.35/0.54          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ X7)
% 0.35/0.54          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X7))
% 0.35/0.54          | (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.35/0.54          | ~ (v1_relat_1 @ X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ sk_D_1)
% 0.35/0.54          | (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.35/0.54          | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1))
% 0.35/0.54          | ~ (r2_hidden @ sk_F @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.54  thf('35', plain, ((v1_relat_1 @ sk_D_1)),
% 0.35/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.35/0.54  thf('36', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.35/0.54  thf('37', plain, ((r2_hidden @ sk_F @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.35/0.54          | ~ (r2_hidden @ sk_F @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.35/0.54  thf('39', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '38'])).
% 0.35/0.54  thf('40', plain, ($false),
% 0.35/0.54      inference('demod', [status(thm)], ['0', '3', '39'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
