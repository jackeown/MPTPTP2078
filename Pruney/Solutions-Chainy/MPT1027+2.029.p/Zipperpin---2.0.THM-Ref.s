%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FS3ptBeY1H

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:59 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 301 expanded)
%              Number of leaves         :   24 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  495 (4042 expanded)
%              Number of equality atoms :   42 ( 188 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('2',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15
       != ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['11','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','16'])).

thf('18',plain,(
    ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['6','17'])).

thf('19',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['2','18'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('21',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['2','18'])).

thf('22',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( v1_funct_2 @ X20 @ X19 @ X18 )
      | ( X20 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,(
    ! [X19: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X19 @ k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('29',plain,(
    ! [X19: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X19 @ k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','27','28'])).

thf('30',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','16'])).

thf('31',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('40',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('44',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('45',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['37','38','39','42','43','44'])).

thf('46',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','45'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('50',plain,(
    ! [X13: $i] :
      ( zip_tseitin_0 @ X13 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['23','47','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FS3ptBeY1H
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:44:21 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 145 iterations in 0.100s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.58  thf(t130_funct_2, conjecture,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.58       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.39/0.58         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.58           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.58        ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.58          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.39/0.58            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.58              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d1_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_2, axiom,
% 0.39/0.58    (![C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_4, axiom,
% 0.39/0.58    (![B:$i,A:$i]:
% 0.39/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.58  thf(zf_stmt_5, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.58         (~ (zip_tseitin_0 @ X18 @ X19)
% 0.39/0.58          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 0.39/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf('3', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.58         (((X15) != (k1_relset_1 @ X15 @ X16 @ X17))
% 0.39/0.58          | (v1_funct_2 @ X17 @ X15 @ X16)
% 0.39/0.58          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      ((((sk_A) != (sk_A))
% 0.39/0.58        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.39/0.58        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.58        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.39/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.58        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.39/0.58         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.39/0.58      inference('split', [status(esa)], ['7'])).
% 0.39/0.58  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('10', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.39/0.58      inference('split', [status(esa)], ['7'])).
% 0.39/0.58  thf('11', plain, (((v1_funct_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.39/0.58      inference('split', [status(esa)], ['7'])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.39/0.58       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.39/0.58       ~ ((v1_funct_1 @ sk_C))),
% 0.39/0.58      inference('split', [status(esa)], ['7'])).
% 0.39/0.58  thf('16', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['11', '14', '15'])).
% 0.39/0.58  thf('17', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['8', '16'])).
% 0.39/0.58  thf('18', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.39/0.58      inference('clc', [status(thm)], ['6', '17'])).
% 0.39/0.58  thf('19', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.39/0.58      inference('clc', [status(thm)], ['2', '18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i]:
% 0.39/0.58         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.39/0.58  thf('21', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.39/0.58      inference('clc', [status(thm)], ['2', '18'])).
% 0.39/0.58  thf('22', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.58  thf('23', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['19', '22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.58         (((X18) != (k1_xboole_0))
% 0.39/0.58          | ((X19) = (k1_xboole_0))
% 0.39/0.58          | (v1_funct_2 @ X20 @ X19 @ X18)
% 0.39/0.58          | ((X20) != (k1_xboole_0))
% 0.39/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X19 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.39/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ k1_xboole_0)))
% 0.39/0.58          | (v1_funct_2 @ k1_xboole_0 @ X19 @ k1_xboole_0)
% 0.39/0.58          | ((X19) = (k1_xboole_0)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.58  thf(t113_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i]:
% 0.39/0.58         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.58  thf(t4_subset_1, axiom,
% 0.39/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X19 : $i]:
% 0.39/0.58         ((v1_funct_2 @ k1_xboole_0 @ X19 @ k1_xboole_0)
% 0.39/0.58          | ((X19) = (k1_xboole_0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['25', '27', '28'])).
% 0.39/0.58  thf('30', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['8', '16'])).
% 0.39/0.58  thf('31', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.58  thf('32', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.39/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t3_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('35', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf(d10_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (![X0 : $i, X2 : $i]:
% 0.39/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 0.39/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('38', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.58  thf('43', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.58  thf('45', plain, (((k1_xboole_0) = (sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['37', '38', '39', '42', '43', '44'])).
% 0.39/0.58  thf('46', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.39/0.58      inference('demod', [status(thm)], ['32', '45'])).
% 0.39/0.58  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['29', '46'])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i]:
% 0.39/0.58         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i]:
% 0.39/0.58         ((zip_tseitin_0 @ X13 @ X14) | ((X14) != (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.39/0.58  thf('50', plain, (![X13 : $i]: (zip_tseitin_0 @ X13 @ k1_xboole_0)),
% 0.39/0.58      inference('simplify', [status(thm)], ['49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.39/0.58      inference('sup+', [status(thm)], ['48', '50'])).
% 0.39/0.58  thf('52', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.39/0.58      inference('eq_fact', [status(thm)], ['51'])).
% 0.39/0.58  thf('53', plain, ($false),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '47', '52'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
