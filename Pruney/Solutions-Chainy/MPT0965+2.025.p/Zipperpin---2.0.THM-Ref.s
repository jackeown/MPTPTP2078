%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ogbC95Jpe8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 104 expanded)
%              Number of leaves         :   37 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  493 ( 943 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['4','11','14'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X17 @ X16 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['17','22','23'])).

thf('25',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('37',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ogbC95Jpe8
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:25:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 66 iterations in 0.088s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(t7_funct_2, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.54       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.54            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.54          ( ( r2_hidden @ C @ A ) =>
% 0.20/0.54            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.20/0.54  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('2', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d1_funct_2, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_1, axiom,
% 0.20/0.54    (![C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.54         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.20/0.54          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.20/0.54          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.20/0.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(zf_stmt_2, axiom,
% 0.20/0.54    (![B:$i,A:$i]:
% 0.20/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_5, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.54         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.20/0.54          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.20/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.54  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.54         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.20/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.20/0.54  thf(t12_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.54         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.20/0.54          | (r2_hidden @ (k1_funct_1 @ X17 @ X16) @ (k2_relat_1 @ X17))
% 0.20/0.54          | ~ (v1_funct_1 @ X17)
% 0.20/0.54          | ~ (v1_relat_1 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.54          | ~ (v1_relat_1 @ sk_D)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.54          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.54          | (v1_relat_1 @ X10)
% 0.20/0.54          | ~ (v1_relat_1 @ X11))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf(fc6_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.54  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.54          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.54      inference('demod', [status(thm)], ['17', '22', '23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.54         ((v5_relat_1 @ X18 @ X20)
% 0.20/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.54  thf('28', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf(d19_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         (~ (v5_relat_1 @ X12 @ X13)
% 0.20/0.54          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.20/0.54          | ~ (v1_relat_1 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf(d1_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.54          | (r2_hidden @ X0 @ X2)
% 0.20/0.54          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.54  thf('35', plain, ((r2_hidden @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['32', '34'])).
% 0.20/0.54  thf(t1_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf(l3_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.54          | (r2_hidden @ X5 @ X7)
% 0.20/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf('40', plain, ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ sk_B)),
% 0.20/0.54      inference('sup-', [status(thm)], ['25', '39'])).
% 0.20/0.54  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
