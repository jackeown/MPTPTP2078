%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a3Eieommpo

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:26 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   83 (  98 expanded)
%              Number of leaves         :   38 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  529 ( 847 expanded)
%              Number of equality atoms :   36 (  52 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v5_relat_1 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
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

thf('5',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_2 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_1 @ X49 @ X50 )
      | ( zip_tseitin_2 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X13 != X12 )
      | ( r2_hidden @ X13 @ X14 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_tarski @ X12 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_1 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( k2_zfmisc_1 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_1 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    zip_tseitin_2 @ sk_D @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X41 )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','19','22'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X36 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X36 @ X35 ) @ X37 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v5_relat_1 @ X36 @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['25','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['2','33'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('38',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a3Eieommpo
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:45:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 107 iterations in 0.076s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.35/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.52  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.35/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.52  thf(t65_funct_2, conjecture,
% 0.35/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.35/0.52         ( m1_subset_1 @
% 0.35/0.52           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.35/0.52       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.35/0.52            ( m1_subset_1 @
% 0.35/0.52              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.35/0.52          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.35/0.52  thf('0', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_D @ 
% 0.35/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(cc2_relset_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.52  thf('1', plain,
% 0.35/0.52      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.35/0.52         ((v5_relat_1 @ X38 @ X40)
% 0.35/0.52          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.52  thf('2', plain, ((v5_relat_1 @ sk_D @ (k1_tarski @ sk_B))),
% 0.35/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.52  thf('3', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(d1_funct_2, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_1, axiom,
% 0.35/0.52    (![C:$i,B:$i,A:$i]:
% 0.35/0.52     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.35/0.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.52  thf('5', plain,
% 0.35/0.52      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.35/0.52         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.35/0.52          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 0.35/0.52          | ~ (zip_tseitin_2 @ X48 @ X47 @ X46))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.52  thf('6', plain,
% 0.35/0.52      ((~ (zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.52        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.52  thf('7', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_D @ 
% 0.35/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.35/0.52  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $o).
% 0.35/0.52  thf(zf_stmt_4, axiom,
% 0.35/0.52    (![B:$i,A:$i]:
% 0.35/0.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.52       ( zip_tseitin_1 @ B @ A ) ))).
% 0.35/0.52  thf(zf_stmt_5, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.52       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.35/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.52  thf('8', plain,
% 0.35/0.52      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.35/0.52         (~ (zip_tseitin_1 @ X49 @ X50)
% 0.35/0.52          | (zip_tseitin_2 @ X51 @ X49 @ X50)
% 0.35/0.52          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      (((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)
% 0.35/0.52        | ~ (zip_tseitin_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.35/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.52  thf(d1_tarski, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.52         (((X13) != (X12))
% 0.35/0.52          | (r2_hidden @ X13 @ X14)
% 0.35/0.52          | ((X14) != (k1_tarski @ X12)))),
% 0.35/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.52  thf('11', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_tarski @ X12))),
% 0.35/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      (![X44 : $i, X45 : $i]:
% 0.35/0.52         ((zip_tseitin_1 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.35/0.52  thf(t113_zfmisc_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.52  thf('13', plain,
% 0.35/0.52      (![X25 : $i, X26 : $i]:
% 0.35/0.52         (((k2_zfmisc_1 @ X25 @ X26) = (k1_xboole_0))
% 0.35/0.52          | ((X26) != (k1_xboole_0)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.35/0.52  thf('14', plain,
% 0.35/0.52      (![X25 : $i]: ((k2_zfmisc_1 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.35/0.52  thf(t152_zfmisc_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.35/0.52  thf('15', plain,
% 0.35/0.52      (![X27 : $i, X28 : $i]: ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X27 @ X28))),
% 0.35/0.52      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.35/0.52  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.52  thf('17', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.52         (~ (r2_hidden @ X1 @ X0) | (zip_tseitin_1 @ X0 @ X2))),
% 0.35/0.52      inference('sup-', [status(thm)], ['12', '16'])).
% 0.35/0.52  thf('18', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]: (zip_tseitin_1 @ (k1_tarski @ X0) @ X1)),
% 0.35/0.52      inference('sup-', [status(thm)], ['11', '17'])).
% 0.35/0.52  thf('19', plain, ((zip_tseitin_2 @ sk_D @ (k1_tarski @ sk_B) @ sk_A)),
% 0.35/0.52      inference('demod', [status(thm)], ['9', '18'])).
% 0.35/0.52  thf('20', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_D @ 
% 0.35/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.52  thf('21', plain,
% 0.35/0.52      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.35/0.52         (((k1_relset_1 @ X42 @ X43 @ X41) = (k1_relat_1 @ X41))
% 0.35/0.52          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.52  thf('22', plain,
% 0.35/0.52      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.35/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.52  thf('23', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.35/0.52      inference('demod', [status(thm)], ['6', '19', '22'])).
% 0.35/0.52  thf(t176_funct_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.52       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.35/0.52         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.35/0.52  thf('24', plain,
% 0.35/0.52      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.35/0.52         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X36))
% 0.35/0.52          | (m1_subset_1 @ (k1_funct_1 @ X36 @ X35) @ X37)
% 0.35/0.52          | ~ (v1_funct_1 @ X36)
% 0.35/0.52          | ~ (v5_relat_1 @ X36 @ X37)
% 0.35/0.52          | ~ (v1_relat_1 @ X36))),
% 0.35/0.52      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.35/0.52  thf('25', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.52          | ~ (v1_relat_1 @ sk_D)
% 0.35/0.52          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.35/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.35/0.52          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.35/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.52  thf('26', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_D @ 
% 0.35/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(cc2_relat_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ A ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.52  thf('27', plain,
% 0.35/0.52      (![X31 : $i, X32 : $i]:
% 0.35/0.52         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.35/0.52          | (v1_relat_1 @ X31)
% 0.35/0.52          | ~ (v1_relat_1 @ X32))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.52  thf('28', plain,
% 0.35/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.35/0.52        | (v1_relat_1 @ sk_D))),
% 0.35/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.52  thf(fc6_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.52  thf('29', plain,
% 0.35/0.52      (![X33 : $i, X34 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X33 @ X34))),
% 0.35/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.52  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.35/0.52  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('32', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.52          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.35/0.52          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.35/0.52      inference('demod', [status(thm)], ['25', '30', '31'])).
% 0.35/0.52  thf('33', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C_1) @ X0)
% 0.35/0.52          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['3', '32'])).
% 0.35/0.52  thf('34', plain,
% 0.35/0.52      ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.35/0.52      inference('sup-', [status(thm)], ['2', '33'])).
% 0.35/0.52  thf(t2_subset, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.52  thf('35', plain,
% 0.35/0.52      (![X29 : $i, X30 : $i]:
% 0.35/0.52         ((r2_hidden @ X29 @ X30)
% 0.35/0.52          | (v1_xboole_0 @ X30)
% 0.35/0.52          | ~ (m1_subset_1 @ X29 @ X30))),
% 0.35/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.52  thf('36', plain,
% 0.35/0.52      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.35/0.52        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.52  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.35/0.52  thf('37', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X23))),
% 0.35/0.52      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.35/0.52  thf('38', plain,
% 0.35/0.52      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B))),
% 0.35/0.52      inference('clc', [status(thm)], ['36', '37'])).
% 0.35/0.52  thf('39', plain,
% 0.35/0.52      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.35/0.52         (~ (r2_hidden @ X15 @ X14)
% 0.35/0.52          | ((X15) = (X12))
% 0.35/0.52          | ((X14) != (k1_tarski @ X12)))),
% 0.35/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.52  thf('40', plain,
% 0.35/0.52      (![X12 : $i, X15 : $i]:
% 0.35/0.52         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.35/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.35/0.52  thf('41', plain, (((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B))),
% 0.35/0.52      inference('sup-', [status(thm)], ['38', '40'])).
% 0.35/0.52  thf('42', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('43', plain, ($false),
% 0.35/0.52      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.35/0.52  
% 0.35/0.52  % SZS output end Refutation
% 0.35/0.52  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
