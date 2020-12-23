%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dbkcph9kqK

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:01 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 233 expanded)
%              Number of leaves         :   27 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :  463 (2996 expanded)
%              Number of equality atoms :   43 ( 168 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('2',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X13
       != ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['6','10'])).

thf('12',plain,(
    ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('14',plain,(
    ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','11'])).

thf('15',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16 != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( v1_funct_2 @ X18 @ X17 @ X16 )
      | ( X18 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,(
    ! [X17: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X17 @ k1_xboole_0 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X17 @ k1_xboole_0 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','20','21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('24',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('25',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('40',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','40'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','41'])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('45',plain,(
    ! [X11: $i] :
      ( zip_tseitin_0 @ X11 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['16','42','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dbkcph9kqK
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:52:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 107 iterations in 0.080s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(t130_funct_2, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.36/0.54         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.54           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.54        ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.54          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.36/0.54            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.54              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d1_funct_2, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_2, axiom,
% 0.36/0.54    (![C:$i,B:$i,A:$i]:
% 0.36/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_4, axiom,
% 0.36/0.54    (![B:$i,A:$i]:
% 0.36/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.54  thf(zf_stmt_5, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.54         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.36/0.54          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.36/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.36/0.54        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf('3', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         (((X13) != (k1_relset_1 @ X13 @ X14 @ X15))
% 0.36/0.54          | (v1_funct_2 @ X15 @ X13 @ X14)
% 0.36/0.54          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      ((((sk_A) != (sk_A))
% 0.36/0.54        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.36/0.54        | (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.36/0.54        | ~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.54        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.36/0.54        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('10', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.36/0.54  thf('11', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('clc', [status(thm)], ['6', '10'])).
% 0.36/0.54  thf('12', plain, (~ (zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('clc', [status(thm)], ['2', '11'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.54  thf('14', plain, (~ (zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('clc', [status(thm)], ['2', '11'])).
% 0.36/0.54  thf('15', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf('16', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.36/0.54      inference('demod', [status(thm)], ['12', '15'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.54         (((X16) != (k1_xboole_0))
% 0.36/0.54          | ((X17) = (k1_xboole_0))
% 0.36/0.54          | (v1_funct_2 @ X18 @ X17 @ X16)
% 0.36/0.54          | ((X18) != (k1_xboole_0))
% 0.36/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X17 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.36/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ k1_xboole_0)))
% 0.36/0.54          | (v1_funct_2 @ k1_xboole_0 @ X17 @ k1_xboole_0)
% 0.36/0.54          | ((X17) = (k1_xboole_0)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.36/0.54  thf(t113_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]:
% 0.36/0.54         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.54  thf(t4_subset_1, axiom,
% 0.36/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.36/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X17 : $i]:
% 0.36/0.54         ((v1_funct_2 @ k1_xboole_0 @ X17 @ k1_xboole_0)
% 0.36/0.54          | ((X17) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '20', '21'])).
% 0.36/0.54  thf('23', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.36/0.54  thf('24', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf('25', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.54  thf(t7_xboole_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.36/0.54      inference('sup+', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t5_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.36/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X8 @ X9)
% 0.36/0.54          | ~ (v1_xboole_0 @ X10)
% 0.36/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.54          | (zip_tseitin_0 @ sk_B_1 @ X1)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['29', '32'])).
% 0.36/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.54  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ sk_B_1 @ X1) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (![X0 : $i]: (((sk_C) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['26', '35'])).
% 0.36/0.54  thf('37', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((sk_C) = (k1_xboole_0)) | (zip_tseitin_0 @ k1_xboole_0 @ X0))),
% 0.36/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.54  thf('39', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.36/0.54      inference('demod', [status(thm)], ['12', '15'])).
% 0.36/0.54  thf('40', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.54  thf('41', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.36/0.54      inference('demod', [status(thm)], ['25', '40'])).
% 0.36/0.54  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['22', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X11 @ X12) | ((X12) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.54  thf('45', plain, (![X11 : $i]: (zip_tseitin_0 @ X11 @ k1_xboole_0)),
% 0.36/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.36/0.54      inference('sup+', [status(thm)], ['43', '45'])).
% 0.36/0.54  thf('47', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.36/0.54      inference('eq_fact', [status(thm)], ['46'])).
% 0.36/0.54  thf('48', plain, ($false),
% 0.36/0.54      inference('demod', [status(thm)], ['16', '42', '47'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
