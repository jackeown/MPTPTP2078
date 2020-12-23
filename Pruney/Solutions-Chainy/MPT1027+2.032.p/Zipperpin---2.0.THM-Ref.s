%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7BwEMHgEvS

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:59 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 155 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  437 (1753 expanded)
%              Number of equality atoms :   39 ( 104 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X15: $i] :
      ( zip_tseitin_0 @ X15 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

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

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17
       != ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','16'])).

thf('18',plain,(
    ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( v1_funct_2 @ X22 @ X21 @ X20 )
      | ( X22 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    ! [X21: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('25',plain,(
    ! [X21: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','23','24'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','17'])).

thf('29',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('36',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('41',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','41'])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['19','43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7BwEMHgEvS
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:27:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 145 iterations in 0.129s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.58  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.58  thf(t8_boole, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X3 : $i, X4 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t8_boole])).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.58  thf(d1_funct_2, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, axiom,
% 0.38/0.58    (![B:$i,A:$i]:
% 0.38/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X15 : $i, X16 : $i]:
% 0.38/0.58         ((zip_tseitin_0 @ X15 @ X16) | ((X16) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('4', plain, (![X15 : $i]: (zip_tseitin_0 @ X15 @ k1_xboole_0)),
% 0.38/0.58      inference('simplify', [status(thm)], ['3'])).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['2', '4'])).
% 0.38/0.58  thf(t130_funct_2, conjecture,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.58       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.38/0.58         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.58           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_1, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.58        ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.58          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.38/0.58            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.58              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.58  thf(zf_stmt_3, axiom,
% 0.38/0.58    (![C:$i,B:$i,A:$i]:
% 0.38/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.58  thf(zf_stmt_5, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.58         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.38/0.58          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.38/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.38/0.58        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf('9', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.58         (((X17) != (k1_relset_1 @ X17 @ X18 @ X19))
% 0.38/0.58          | (v1_funct_2 @ X19 @ X17 @ X18)
% 0.38/0.58          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      ((((sk_A) != (sk_A))
% 0.38/0.58        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.38/0.58        | (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.38/0.58        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.38/0.58        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('16', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.38/0.58  thf('17', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['12', '16'])).
% 0.38/0.58  thf('18', plain, (~ (zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['8', '17'])).
% 0.38/0.58  thf('19', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.58         (((X20) != (k1_xboole_0))
% 0.38/0.58          | ((X21) = (k1_xboole_0))
% 0.38/0.58          | (v1_funct_2 @ X22 @ X21 @ X20)
% 0.38/0.58          | ((X22) != (k1_xboole_0))
% 0.38/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X21 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.38/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ k1_xboole_0)))
% 0.38/0.58          | (v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0)
% 0.38/0.58          | ((X21) = (k1_xboole_0)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.58  thf(t113_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.58  thf(t4_subset_1, axiom,
% 0.38/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X21 : $i]:
% 0.38/0.58         ((v1_funct_2 @ k1_xboole_0 @ X21 @ k1_xboole_0)
% 0.38/0.58          | ((X21) = (k1_xboole_0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['21', '23', '24'])).
% 0.38/0.58  thf('26', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X15 : $i, X16 : $i]:
% 0.38/0.58         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('28', plain, (~ (zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['8', '17'])).
% 0.38/0.58  thf('29', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.58  thf('30', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['26', '29'])).
% 0.38/0.58  thf(d1_xboole_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf(t5_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.58          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X12 @ X13)
% 0.38/0.58          | ~ (v1_xboole_0 @ X14)
% 0.38/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.58  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.58  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.38/0.58      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.38/0.58  thf('39', plain, ((v1_xboole_0 @ sk_C)),
% 0.38/0.58      inference('sup-', [status(thm)], ['31', '38'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.58  thf('41', plain, (((k1_xboole_0) = (sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.58  thf('42', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['30', '41'])).
% 0.38/0.58  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['25', '42'])).
% 0.38/0.58  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.58  thf('45', plain, ($false),
% 0.38/0.58      inference('demod', [status(thm)], ['19', '43', '44'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
