%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z8SWWlpEho

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:57 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 317 expanded)
%              Number of leaves         :   24 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  474 (4183 expanded)
%              Number of equality atoms :   41 ( 199 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X6: $i] :
      ( zip_tseitin_0 @ X6 @ k1_xboole_0 ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X12 )
      | ( zip_tseitin_1 @ X13 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8
       != ( k1_relset_1 @ X8 @ X9 @ X10 ) )
      | ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( zip_tseitin_1 @ X10 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('20',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['15','18','19'])).

thf('21',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['12','20'])).

thf('22',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['10','21'])).

thf('23',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['6','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X11 != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( v1_funct_2 @ X13 @ X12 @ X11 )
      | ( X13 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,(
    ! [X12: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X12 @ k1_xboole_0 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['6','22'])).

thf('32',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X12: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X12 @ k1_xboole_0 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','28','44'])).

thf('46',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['12','20'])).

thf('47',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('48',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['24','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z8SWWlpEho
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 126 iterations in 0.135s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.58  thf(l13_xboole_0, axiom,
% 0.38/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
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
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         ((zip_tseitin_0 @ X6 @ X7) | ((X7) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('2', plain, (![X6 : $i]: (zip_tseitin_0 @ X6 @ k1_xboole_0)),
% 0.38/0.58      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['0', '2'])).
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
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
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
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.58         (~ (zip_tseitin_0 @ X11 @ X12)
% 0.38/0.58          | (zip_tseitin_1 @ X13 @ X11 @ X12)
% 0.38/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.58  thf('7', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.58         (((X8) != (k1_relset_1 @ X8 @ X9 @ X10))
% 0.38/0.58          | (v1_funct_2 @ X10 @ X8 @ X9)
% 0.38/0.58          | ~ (zip_tseitin_1 @ X10 @ X9 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      ((((sk_A) != (sk_A))
% 0.38/0.58        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.38/0.58        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.38/0.58        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.38/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.38/0.58        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.38/0.58         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.38/0.58      inference('split', [status(esa)], ['11'])).
% 0.38/0.58  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('14', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.38/0.58      inference('split', [status(esa)], ['11'])).
% 0.38/0.58  thf('15', plain, (((v1_funct_1 @ sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.38/0.58         <= (~
% 0.38/0.58             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.38/0.58      inference('split', [status(esa)], ['11'])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.38/0.58       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.38/0.58       ~ ((v1_funct_1 @ sk_C))),
% 0.38/0.58      inference('split', [status(esa)], ['11'])).
% 0.38/0.58  thf('20', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['15', '18', '19'])).
% 0.38/0.58  thf('21', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['12', '20'])).
% 0.38/0.58  thf('22', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['10', '21'])).
% 0.38/0.58  thf('23', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['6', '22'])).
% 0.38/0.58  thf('24', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.58      inference('sup-', [status(thm)], ['3', '23'])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.58         (((X11) != (k1_xboole_0))
% 0.38/0.58          | ((X12) = (k1_xboole_0))
% 0.38/0.58          | (v1_funct_2 @ X13 @ X12 @ X11)
% 0.38/0.58          | ((X13) != (k1_xboole_0))
% 0.38/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X12 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.38/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ k1_xboole_0)))
% 0.38/0.58          | (v1_funct_2 @ k1_xboole_0 @ X12 @ k1_xboole_0)
% 0.38/0.58          | ((X12) = (k1_xboole_0)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.58  thf(t113_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X2 : $i, X3 : $i]:
% 0.38/0.58         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         ((zip_tseitin_0 @ X6 @ X7) | ((X6) = (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('31', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['6', '22'])).
% 0.38/0.58  thf('32', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.58  thf('34', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.58  thf(cc1_subset_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (![X4 : $i, X5 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.38/0.58          | (v1_xboole_0 @ X4)
% 0.38/0.58          | ~ (v1_xboole_0 @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.38/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.58  thf('38', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.38/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.58  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.58  thf('41', plain, ((v1_xboole_0 @ sk_C)),
% 0.38/0.58      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.58  thf('43', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.58  thf('44', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['34', '43'])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (![X12 : $i]:
% 0.38/0.58         ((v1_funct_2 @ k1_xboole_0 @ X12 @ k1_xboole_0)
% 0.38/0.58          | ((X12) = (k1_xboole_0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['26', '28', '44'])).
% 0.38/0.58  thf('46', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['12', '20'])).
% 0.38/0.58  thf('47', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf('48', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.38/0.58  thf('49', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.58  thf('50', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.38/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.58  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['45', '50'])).
% 0.38/0.58  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.58  thf('53', plain, ($false),
% 0.38/0.58      inference('demod', [status(thm)], ['24', '51', '52'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
