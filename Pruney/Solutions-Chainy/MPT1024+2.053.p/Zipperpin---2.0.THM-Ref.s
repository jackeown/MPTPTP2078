%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yhVdT7MXpJ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:41 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 174 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  526 (2260 expanded)
%              Number of equality atoms :   18 (  75 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
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

thf('5',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X21
       != ( k9_relat_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r2_hidden @ X22 @ ( k9_relat_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( X27
       != ( k1_funct_1 @ X26 @ X25 ) )
      | ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( r2_hidden @ ( k4_tarski @ X25 @ ( k1_funct_1 @ X26 @ X25 ) ) @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ) @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k1_funct_1 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['19','22','23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X32: $i] :
      ( ~ ( r2_hidden @ X32 @ sk_A )
      | ~ ( r2_hidden @ X32 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('35',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yhVdT7MXpJ
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:31:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.56  % Solved by: fo/fo7.sh
% 0.40/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.56  % done 63 iterations in 0.059s
% 0.40/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.56  % SZS output start Refutation
% 0.40/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.56  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.40/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.40/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.56  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.40/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.40/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.56  thf(t115_funct_2, conjecture,
% 0.40/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.56       ( ![E:$i]:
% 0.40/0.56         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.40/0.56              ( ![F:$i]:
% 0.40/0.56                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.40/0.56                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.40/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.56          ( ![E:$i]:
% 0.40/0.56            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.40/0.56                 ( ![F:$i]:
% 0.40/0.56                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.40/0.56                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.40/0.56    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.40/0.56  thf('0', plain,
% 0.40/0.56      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('1', plain,
% 0.40/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.40/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.40/0.56  thf('2', plain,
% 0.40/0.56      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.56         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.40/0.56          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.40/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.40/0.56  thf('3', plain,
% 0.40/0.56      (![X0 : $i]:
% 0.40/0.56         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.40/0.56           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.40/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.56  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.40/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.40/0.56  thf(d12_funct_1, axiom,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.40/0.56       ( ![B:$i,C:$i]:
% 0.40/0.56         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.40/0.56           ( ![D:$i]:
% 0.40/0.56             ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.56               ( ?[E:$i]:
% 0.40/0.56                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.40/0.56                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.40/0.56  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.56  thf(zf_stmt_2, axiom,
% 0.40/0.56    (![E:$i,D:$i,B:$i,A:$i]:
% 0.40/0.56     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.40/0.56       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.40/0.56         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.40/0.56  thf(zf_stmt_3, axiom,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.56       ( ![B:$i,C:$i]:
% 0.40/0.56         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.40/0.56           ( ![D:$i]:
% 0.40/0.56             ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.56               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.40/0.56  thf('5', plain,
% 0.40/0.56      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.40/0.56         (((X21) != (k9_relat_1 @ X19 @ X18))
% 0.40/0.56          | (zip_tseitin_0 @ (sk_E_1 @ X22 @ X18 @ X19) @ X22 @ X18 @ X19)
% 0.40/0.56          | ~ (r2_hidden @ X22 @ X21)
% 0.40/0.56          | ~ (v1_funct_1 @ X19)
% 0.40/0.56          | ~ (v1_relat_1 @ X19))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.56  thf('6', plain,
% 0.40/0.56      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.40/0.56         (~ (v1_relat_1 @ X19)
% 0.40/0.56          | ~ (v1_funct_1 @ X19)
% 0.40/0.56          | ~ (r2_hidden @ X22 @ (k9_relat_1 @ X19 @ X18))
% 0.40/0.56          | (zip_tseitin_0 @ (sk_E_1 @ X22 @ X18 @ X19) @ X22 @ X18 @ X19))),
% 0.40/0.56      inference('simplify', [status(thm)], ['5'])).
% 0.40/0.56  thf('7', plain,
% 0.40/0.56      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.40/0.56         sk_D_1)
% 0.40/0.56        | ~ (v1_funct_1 @ sk_D_1)
% 0.40/0.56        | ~ (v1_relat_1 @ sk_D_1))),
% 0.40/0.56      inference('sup-', [status(thm)], ['4', '6'])).
% 0.40/0.56  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('9', plain,
% 0.40/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(cc2_relat_1, axiom,
% 0.40/0.56    (![A:$i]:
% 0.40/0.56     ( ( v1_relat_1 @ A ) =>
% 0.40/0.56       ( ![B:$i]:
% 0.40/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.56  thf('10', plain,
% 0.40/0.56      (![X8 : $i, X9 : $i]:
% 0.40/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.40/0.56          | (v1_relat_1 @ X8)
% 0.40/0.56          | ~ (v1_relat_1 @ X9))),
% 0.40/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.56  thf('11', plain,
% 0.40/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.40/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.56  thf(fc6_relat_1, axiom,
% 0.40/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.56  thf('12', plain,
% 0.40/0.56      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.40/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.56  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.40/0.56      inference('demod', [status(thm)], ['11', '12'])).
% 0.40/0.56  thf('14', plain,
% 0.40/0.56      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.40/0.56        sk_D_1)),
% 0.40/0.56      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.40/0.56  thf('15', plain,
% 0.40/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.56         ((r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.40/0.56          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.56  thf('16', plain,
% 0.40/0.56      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.40/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.56  thf(t8_funct_1, axiom,
% 0.40/0.56    (![A:$i,B:$i,C:$i]:
% 0.40/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.40/0.56         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.40/0.56           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.40/0.56  thf('17', plain,
% 0.40/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.56         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.40/0.56          | ((X27) != (k1_funct_1 @ X26 @ X25))
% 0.40/0.56          | (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.40/0.56          | ~ (v1_funct_1 @ X26)
% 0.40/0.56          | ~ (v1_relat_1 @ X26))),
% 0.40/0.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.40/0.56  thf('18', plain,
% 0.40/0.56      (![X25 : $i, X26 : $i]:
% 0.40/0.56         (~ (v1_relat_1 @ X26)
% 0.40/0.56          | ~ (v1_funct_1 @ X26)
% 0.40/0.56          | (r2_hidden @ (k4_tarski @ X25 @ (k1_funct_1 @ X26 @ X25)) @ X26)
% 0.40/0.56          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X26)))),
% 0.40/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.40/0.56  thf('19', plain,
% 0.40/0.56      (((r2_hidden @ 
% 0.40/0.56         (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ 
% 0.40/0.56          (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1))) @ 
% 0.40/0.56         sk_D_1)
% 0.40/0.56        | ~ (v1_funct_1 @ sk_D_1)
% 0.40/0.56        | ~ (v1_relat_1 @ sk_D_1))),
% 0.40/0.56      inference('sup-', [status(thm)], ['16', '18'])).
% 0.40/0.56  thf('20', plain,
% 0.40/0.56      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.40/0.56        sk_D_1)),
% 0.40/0.56      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.40/0.56  thf('21', plain,
% 0.40/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.56         (((X14) = (k1_funct_1 @ X12 @ X13))
% 0.40/0.56          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.56  thf('22', plain,
% 0.40/0.56      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.40/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.56  thf('23', plain, ((v1_funct_1 @ sk_D_1)),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('24', plain, ((v1_relat_1 @ sk_D_1)),
% 0.40/0.56      inference('demod', [status(thm)], ['11', '12'])).
% 0.40/0.56  thf('25', plain,
% 0.40/0.56      ((r2_hidden @ (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ 
% 0.40/0.56        sk_D_1)),
% 0.40/0.56      inference('demod', [status(thm)], ['19', '22', '23', '24'])).
% 0.40/0.56  thf('26', plain,
% 0.40/0.56      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf(l3_subset_1, axiom,
% 0.40/0.56    (![A:$i,B:$i]:
% 0.40/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.40/0.56  thf('27', plain,
% 0.40/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.56         (~ (r2_hidden @ X5 @ X6)
% 0.40/0.56          | (r2_hidden @ X5 @ X7)
% 0.40/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.40/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.40/0.56  thf('28', plain,
% 0.40/0.56      (![X0 : $i]:
% 0.40/0.56         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.40/0.56          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.40/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.56  thf('29', plain,
% 0.40/0.56      ((r2_hidden @ (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ 
% 0.40/0.56        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.40/0.56      inference('sup-', [status(thm)], ['25', '28'])).
% 0.40/0.56  thf(l54_zfmisc_1, axiom,
% 0.40/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.56     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.40/0.56       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.40/0.56  thf('30', plain,
% 0.40/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.56         ((r2_hidden @ X0 @ X1)
% 0.40/0.56          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.40/0.56      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.40/0.56  thf('31', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.40/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.56  thf('32', plain,
% 0.40/0.56      (![X32 : $i]:
% 0.40/0.56         (~ (r2_hidden @ X32 @ sk_A)
% 0.40/0.56          | ~ (r2_hidden @ X32 @ sk_C)
% 0.40/0.56          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X32)))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.56  thf('33', plain,
% 0.40/0.56      ((((sk_E_2) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))
% 0.40/0.56        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C))),
% 0.40/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.56  thf('34', plain,
% 0.40/0.56      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.40/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.56  thf('35', plain,
% 0.40/0.56      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.40/0.56        sk_D_1)),
% 0.40/0.56      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.40/0.56  thf('36', plain,
% 0.40/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.56         ((r2_hidden @ X13 @ X15) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.40/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.56  thf('37', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.40/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.56  thf('38', plain, (((sk_E_2) != (sk_E_2))),
% 0.40/0.56      inference('demod', [status(thm)], ['33', '34', '37'])).
% 0.40/0.56  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.40/0.56  
% 0.40/0.56  % SZS output end Refutation
% 0.40/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
