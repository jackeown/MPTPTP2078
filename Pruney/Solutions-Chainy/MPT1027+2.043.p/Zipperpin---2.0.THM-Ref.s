%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HvXhjhkS0f

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 356 expanded)
%              Number of leaves         :   23 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          :  477 (4835 expanded)
%              Number of equality atoms :   42 ( 227 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X13 )
      | ( zip_tseitin_1 @ X14 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9
       != ( k1_relset_1 @ X9 @ X10 @ X11 ) )
      | ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( zip_tseitin_1 @ X11 @ X10 @ X9 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 )
      | ( X7 = k1_xboole_0 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( v1_funct_2 @ X14 @ X13 @ X12 )
      | ( X14 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,(
    ! [X13: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X13 @ k1_xboole_0 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('30',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('36',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('37',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('39',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X13: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X13 @ k1_xboole_0 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','27','40'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','16'])).

thf('43',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('44',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('46',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('50',plain,(
    ! [X7: $i] :
      ( zip_tseitin_0 @ X7 @ k1_xboole_0 ) ),
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
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HvXhjhkS0f
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:31:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 107 iterations in 0.081s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(t130_funct_2, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.21/0.54         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.54           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.54        ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.21/0.54            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.54              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d1_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_2, axiom,
% 0.21/0.54    (![C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_4, axiom,
% 0.21/0.54    (![B:$i,A:$i]:
% 0.21/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.54  thf(zf_stmt_5, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (zip_tseitin_0 @ X12 @ X13)
% 0.21/0.54          | (zip_tseitin_1 @ X14 @ X12 @ X13)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((X9) != (k1_relset_1 @ X9 @ X10 @ X11))
% 0.21/0.54          | (v1_funct_2 @ X11 @ X9 @ X10)
% 0.21/0.54          | ~ (zip_tseitin_1 @ X11 @ X10 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      ((((sk_A) != (sk_A))
% 0.21/0.54        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.54        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['7'])).
% 0.21/0.54  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('10', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.21/0.54      inference('split', [status(esa)], ['7'])).
% 0.21/0.54  thf('11', plain, (((v1_funct_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.21/0.54      inference('split', [status(esa)], ['7'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.21/0.54       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.21/0.54       ~ ((v1_funct_1 @ sk_C))),
% 0.21/0.54      inference('split', [status(esa)], ['7'])).
% 0.21/0.54  thf('16', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['11', '14', '15'])).
% 0.21/0.54  thf('17', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['8', '16'])).
% 0.21/0.54  thf('18', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['6', '17'])).
% 0.21/0.54  thf('19', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['2', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X7 @ X8) | ((X7) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.54  thf('21', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['2', '18'])).
% 0.21/0.54  thf('22', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (((X12) != (k1_xboole_0))
% 0.21/0.54          | ((X13) = (k1_xboole_0))
% 0.21/0.54          | (v1_funct_2 @ X14 @ X13 @ X12)
% 0.21/0.54          | ((X14) != (k1_xboole_0))
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X13 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ k1_xboole_0)))
% 0.21/0.54          | (v1_funct_2 @ k1_xboole_0 @ X13 @ k1_xboole_0)
% 0.21/0.54          | ((X13) = (k1_xboole_0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.54  thf(t113_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]:
% 0.21/0.54         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('29', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.54  thf('31', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('34', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('35', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.54  thf('37', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.54  thf(t3_xboole_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.54  thf('39', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('40', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['31', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X13 : $i]:
% 0.21/0.54         ((v1_funct_2 @ k1_xboole_0 @ X13 @ k1_xboole_0)
% 0.21/0.54          | ((X13) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['25', '27', '40'])).
% 0.21/0.54  thf('42', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['8', '16'])).
% 0.21/0.54  thf('43', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('44', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('46', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X7 @ X8) | ((X7) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X7 @ X8) | ((X8) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.54  thf('50', plain, (![X7 : $i]: (zip_tseitin_0 @ X7 @ k1_xboole_0)),
% 0.21/0.54      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.21/0.54      inference('sup+', [status(thm)], ['48', '50'])).
% 0.21/0.54  thf('52', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.21/0.54      inference('eq_fact', [status(thm)], ['51'])).
% 0.21/0.54  thf('53', plain, ($false),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '47', '52'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
