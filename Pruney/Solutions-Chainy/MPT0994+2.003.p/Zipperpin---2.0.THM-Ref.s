%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L2PR7Oi8IL

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 100 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  530 (1314 expanded)
%              Number of equality atoms :   34 (  78 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t41_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( r2_hidden @ C @ A )
          & ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C )
            = ( k1_funct_1 @ E @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( ( v1_funct_1 @ E )
          & ( v1_funct_2 @ E @ A @ B )
          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( r2_hidden @ C @ A )
            & ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) )
         => ( ( B = k1_xboole_0 )
            | ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C )
              = ( k1_funct_1 @ E @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_funct_2])).

thf('0',plain,(
    ( k1_funct_1 @ ( k6_relset_1 @ sk_A @ sk_B @ sk_D @ sk_E ) @ sk_C )
 != ( k1_funct_1 @ sk_E @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k6_relset_1 @ X15 @ X16 @ X13 @ X14 )
        = ( k8_relat_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_E )
      = ( k8_relat_1 @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_E @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_B ),
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

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    zip_tseitin_1 @ sk_E @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf(t86_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X5 @ X4 ) @ X6 )
      | ( r2_hidden @ X4 @ ( k1_relat_1 @ ( k8_relat_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t86_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ sk_E ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_E @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ sk_E ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_E @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t87_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
       => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X8 @ X9 ) @ X7 )
        = ( k1_funct_1 @ X9 @ X7 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t87_funct_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
      = ( k1_funct_1 @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['23','24'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
    = ( k1_funct_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ( k1_funct_1 @ sk_E @ sk_C )
 != ( k1_funct_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['0','3','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L2PR7Oi8IL
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 61 iterations in 0.083s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(t41_funct_2, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.54     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.20/0.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.54       ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) ) =>
% 0.20/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54           ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C ) =
% 0.20/0.54             ( k1_funct_1 @ E @ C ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.54        ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.20/0.54            ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.54          ( ( ( r2_hidden @ C @ A ) & 
% 0.20/0.54              ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) ) =>
% 0.20/0.54            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54              ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C ) =
% 0.20/0.54                ( k1_funct_1 @ E @ C ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t41_funct_2])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((k1_funct_1 @ (k6_relset_1 @ sk_A @ sk_B @ sk_D @ sk_E) @ sk_C)
% 0.20/0.54         != (k1_funct_1 @ sk_E @ sk_C))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k6_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (((k6_relset_1 @ X15 @ X16 @ X13 @ X14) = (k8_relat_1 @ X13 @ X14))
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_E) = (k8_relat_1 @ X0 @ sk_E))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf('4', plain, ((r2_hidden @ (k1_funct_1 @ sk_E @ sk_C) @ sk_D)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('5', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_B)),
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
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.54         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.20/0.54          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.20/0.54          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      ((~ (zip_tseitin_1 @ sk_E @ sk_B @ sk_A)
% 0.20/0.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_E)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf(zf_stmt_2, axiom,
% 0.20/0.54    (![B:$i,A:$i]:
% 0.20/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
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
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.54         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.20/0.54          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.20/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (((zip_tseitin_1 @ sk_E @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_B @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.54  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('14', plain, ((zip_tseitin_1 @ sk_E @ sk_B @ sk_A)),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.54         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.20/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 0.20/0.54      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.20/0.54  thf(t86_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.20/0.54         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.54           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X4 @ (k1_relat_1 @ X5))
% 0.20/0.54          | ~ (r2_hidden @ (k1_funct_1 @ X5 @ X4) @ X6)
% 0.20/0.54          | (r2_hidden @ X4 @ (k1_relat_1 @ (k8_relat_1 @ X6 @ X5)))
% 0.20/0.54          | ~ (v1_funct_1 @ X5)
% 0.20/0.54          | ~ (v1_relat_1 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [t86_funct_1])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.54          | ~ (v1_relat_1 @ sk_E)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.54          | (r2_hidden @ X0 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ sk_E)))
% 0.20/0.54          | ~ (r2_hidden @ (k1_funct_1 @ sk_E @ X0) @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.54          | (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_E))),
% 0.20/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf(fc6_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.54  thf('25', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.54          | (r2_hidden @ X0 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ sk_E)))
% 0.20/0.54          | ~ (r2_hidden @ (k1_funct_1 @ sk_E @ X0) @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '25', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (((r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ sk_D @ sk_E)))
% 0.20/0.54        | ~ (r2_hidden @ sk_C @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '27'])).
% 0.20/0.54  thf('29', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ sk_D @ sk_E)))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf(t87_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.20/0.54         ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X7 @ (k1_relat_1 @ (k8_relat_1 @ X8 @ X9)))
% 0.20/0.54          | ((k1_funct_1 @ (k8_relat_1 @ X8 @ X9) @ X7)
% 0.20/0.54              = (k1_funct_1 @ X9 @ X7))
% 0.20/0.54          | ~ (v1_funct_1 @ X9)
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t87_funct_1])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_E)
% 0.20/0.54        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.54        | ((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C)
% 0.20/0.54            = (k1_funct_1 @ sk_E @ sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('33', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C)
% 0.20/0.54         = (k1_funct_1 @ sk_E @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (((k1_funct_1 @ sk_E @ sk_C) != (k1_funct_1 @ sk_E @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '3', '35'])).
% 0.20/0.54  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
