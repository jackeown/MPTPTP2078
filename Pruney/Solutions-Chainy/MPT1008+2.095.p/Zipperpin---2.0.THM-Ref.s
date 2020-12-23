%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jrxq086ofP

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:44 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 154 expanded)
%              Number of leaves         :   37 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  537 (1839 expanded)
%              Number of equality atoms :   45 ( 141 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf(t168_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ ( k1_tarski @ X14 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t168_funct_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('32',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('34',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','23','24','25','34'])).

thf('36',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jrxq086ofP
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:05:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.34/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.55  % Solved by: fo/fo7.sh
% 0.34/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.55  % done 68 iterations in 0.091s
% 0.34/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.55  % SZS output start Refutation
% 0.34/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.34/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.34/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.34/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.34/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.34/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.34/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.34/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.55  thf(t62_funct_2, conjecture,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.34/0.55         ( m1_subset_1 @
% 0.34/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.34/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.34/0.55         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.34/0.55           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.34/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.34/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.34/0.55            ( m1_subset_1 @
% 0.34/0.55              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.34/0.55          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.34/0.55            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.34/0.55              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.34/0.55    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.34/0.55  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(d1_funct_2, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.34/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.34/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.34/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.34/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.34/0.55  thf(zf_stmt_1, axiom,
% 0.34/0.55    (![C:$i,B:$i,A:$i]:
% 0.34/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.34/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.34/0.55  thf('1', plain,
% 0.34/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.34/0.55         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.34/0.55          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.34/0.55          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.34/0.55  thf('2', plain,
% 0.34/0.55      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.34/0.55        | ((k1_tarski @ sk_A)
% 0.34/0.55            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.55  thf(zf_stmt_2, axiom,
% 0.34/0.55    (![B:$i,A:$i]:
% 0.34/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.55       ( zip_tseitin_0 @ B @ A ) ))).
% 0.34/0.55  thf('3', plain,
% 0.34/0.55      (![X27 : $i, X28 : $i]:
% 0.34/0.55         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.34/0.55  thf('4', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.34/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.34/0.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.34/0.55  thf(zf_stmt_5, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.34/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.34/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.34/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.34/0.55  thf('5', plain,
% 0.34/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.34/0.55         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.34/0.55          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.34/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.34/0.55  thf('6', plain,
% 0.34/0.55      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.34/0.55        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.34/0.55  thf('7', plain,
% 0.34/0.55      ((((sk_B_1) = (k1_xboole_0))
% 0.34/0.55        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.34/0.55      inference('sup-', [status(thm)], ['3', '6'])).
% 0.34/0.55  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('9', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.34/0.55      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.34/0.55  thf('10', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.34/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.34/0.55  thf('11', plain,
% 0.34/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.34/0.55         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.34/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.34/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.34/0.55  thf('12', plain,
% 0.34/0.55      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.34/0.55         = (k1_relat_1 @ sk_C_1))),
% 0.34/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.55  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.34/0.55      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.34/0.55  thf(d1_tarski, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.34/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.34/0.55  thf('14', plain,
% 0.34/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.55         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.34/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.34/0.55  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.34/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.34/0.55  thf('16', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.34/0.55      inference('sup+', [status(thm)], ['13', '15'])).
% 0.34/0.55  thf(t168_funct_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.55       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.34/0.55         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.34/0.55           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.34/0.55  thf('17', plain,
% 0.34/0.55      (![X14 : $i, X15 : $i]:
% 0.34/0.55         (~ (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.34/0.55          | ((k2_relat_1 @ (k7_relat_1 @ X15 @ (k1_tarski @ X14)))
% 0.34/0.55              = (k1_tarski @ (k1_funct_1 @ X15 @ X14)))
% 0.34/0.55          | ~ (v1_funct_1 @ X15)
% 0.34/0.55          | ~ (v1_relat_1 @ X15))),
% 0.34/0.55      inference('cnf', [status(esa)], [t168_funct_1])).
% 0.34/0.55  thf('18', plain,
% 0.34/0.55      ((~ (v1_relat_1 @ sk_C_1)
% 0.34/0.55        | ~ (v1_funct_1 @ sk_C_1)
% 0.34/0.55        | ((k2_relat_1 @ (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.34/0.55            = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.55  thf('19', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.34/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(cc2_relat_1, axiom,
% 0.34/0.55    (![A:$i]:
% 0.34/0.55     ( ( v1_relat_1 @ A ) =>
% 0.34/0.55       ( ![B:$i]:
% 0.34/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.34/0.55  thf('20', plain,
% 0.34/0.55      (![X8 : $i, X9 : $i]:
% 0.34/0.55         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.34/0.55          | (v1_relat_1 @ X8)
% 0.34/0.55          | ~ (v1_relat_1 @ X9))),
% 0.34/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.34/0.55  thf('21', plain,
% 0.34/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.34/0.55        | (v1_relat_1 @ sk_C_1))),
% 0.34/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.55  thf(fc6_relat_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.34/0.55  thf('22', plain,
% 0.34/0.55      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.34/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.34/0.55  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.34/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.34/0.55  thf('24', plain, ((v1_funct_1 @ sk_C_1)),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('25', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.34/0.55      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.34/0.55  thf('26', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.34/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(cc2_relset_1, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.55  thf('27', plain,
% 0.34/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.34/0.55         ((v4_relat_1 @ X16 @ X17)
% 0.34/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.34/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.55  thf('28', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.34/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.34/0.55  thf(t209_relat_1, axiom,
% 0.34/0.55    (![A:$i,B:$i]:
% 0.34/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.34/0.55       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.34/0.55  thf('29', plain,
% 0.34/0.55      (![X12 : $i, X13 : $i]:
% 0.34/0.55         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.34/0.55          | ~ (v4_relat_1 @ X12 @ X13)
% 0.34/0.55          | ~ (v1_relat_1 @ X12))),
% 0.34/0.55      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.34/0.55  thf('30', plain,
% 0.34/0.55      ((~ (v1_relat_1 @ sk_C_1)
% 0.34/0.55        | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.34/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.34/0.55  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.34/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.34/0.55  thf('32', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.34/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.34/0.55  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.34/0.55      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.34/0.55  thf('34', plain,
% 0.34/0.55      (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.34/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.34/0.55  thf('35', plain,
% 0.34/0.55      (((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.34/0.55      inference('demod', [status(thm)], ['18', '23', '24', '25', '34'])).
% 0.34/0.55  thf('36', plain,
% 0.34/0.55      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.34/0.55         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf('37', plain,
% 0.34/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.34/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.34/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.34/0.55    (![A:$i,B:$i,C:$i]:
% 0.34/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.34/0.55  thf('38', plain,
% 0.34/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.55         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.34/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.34/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.34/0.55  thf('39', plain,
% 0.34/0.55      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.34/0.55         = (k2_relat_1 @ sk_C_1))),
% 0.34/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.34/0.55  thf('40', plain,
% 0.34/0.55      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.34/0.55      inference('demod', [status(thm)], ['36', '39'])).
% 0.34/0.55  thf('41', plain, ($false),
% 0.34/0.55      inference('simplify_reflect-', [status(thm)], ['35', '40'])).
% 0.34/0.55  
% 0.34/0.55  % SZS output end Refutation
% 0.34/0.55  
% 0.34/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
