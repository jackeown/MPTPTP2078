%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A6Iri36955

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:00 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 117 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  434 (1209 expanded)
%              Number of equality atoms :   41 (  75 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X12: $i] :
      ( zip_tseitin_0 @ X12 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14
       != ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['10','14'])).

thf('16',plain,(
    ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['6','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['6','15'])).

thf('29',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('31',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['26','29','31','32'])).

thf('34',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['22','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X8: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['17','41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A6Iri36955
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:21:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 124 iterations in 0.106s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(l13_xboole_0, axiom,
% 0.42/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.60  thf(d1_funct_2, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, axiom,
% 0.42/0.60    (![B:$i,A:$i]:
% 0.42/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X12 : $i, X13 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X12 @ X13) | ((X13) != (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('2', plain, (![X12 : $i]: (zip_tseitin_0 @ X12 @ k1_xboole_0)),
% 0.42/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['0', '2'])).
% 0.42/0.61  thf(t130_funct_2, conjecture,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.61       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.42/0.61         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.61           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.42/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.61        ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.61          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.42/0.61            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.61              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_3, axiom,
% 0.42/0.61    (![C:$i,B:$i,A:$i]:
% 0.42/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_5, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.42/0.61         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.42/0.61          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (((zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A)
% 0.42/0.61        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.61  thf('7', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C) = (sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.61         (((X14) != (k1_relset_1 @ X14 @ X15 @ X16))
% 0.42/0.61          | (v1_funct_2 @ X16 @ X14 @ X15)
% 0.42/0.61          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      ((((sk_A) != (sk_A))
% 0.42/0.61        | ~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A)
% 0.42/0.61        | (v1_funct_2 @ sk_C @ sk_A @ sk_B_2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.42/0.61        | ~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A))),
% 0.42/0.61      inference('simplify', [status(thm)], ['9'])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.42/0.61        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('14', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 0.42/0.61      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.42/0.61  thf('15', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ sk_A)),
% 0.42/0.61      inference('clc', [status(thm)], ['10', '14'])).
% 0.42/0.61  thf('16', plain, (~ (zip_tseitin_0 @ sk_B_2 @ sk_A)),
% 0.42/0.61      inference('clc', [status(thm)], ['6', '15'])).
% 0.42/0.61  thf('17', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.61      inference('sup-', [status(thm)], ['3', '16'])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.42/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.61  thf('21', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C) = (sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('22', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.42/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.42/0.61  thf(t7_xboole_0, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(t5_subset, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.42/0.61          ( v1_xboole_0 @ C ) ) ))).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X5 @ X6)
% 0.42/0.61          | ~ (v1_xboole_0 @ X7)
% 0.42/0.61          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.42/0.61          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X12 : $i, X13 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('28', plain, (~ (zip_tseitin_0 @ sk_B_2 @ sk_A)),
% 0.42/0.61      inference('clc', [status(thm)], ['6', '15'])).
% 0.42/0.61  thf('29', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.61  thf(t113_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X3 : $i, X4 : $i]:
% 0.42/0.61         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('simplify', [status(thm)], ['30'])).
% 0.42/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.61  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.42/0.61      inference('demod', [status(thm)], ['26', '29', '31', '32'])).
% 0.42/0.61  thf('34', plain, (((sk_C) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['23', '33'])).
% 0.42/0.61  thf('35', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['22', '34'])).
% 0.42/0.61  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf(fc10_relat_1, axiom,
% 0.42/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      (![X8 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.61  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['36', '39'])).
% 0.42/0.61  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['35', '40'])).
% 0.42/0.61  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf('43', plain, ($false),
% 0.42/0.61      inference('demod', [status(thm)], ['17', '41', '42'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.47/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
