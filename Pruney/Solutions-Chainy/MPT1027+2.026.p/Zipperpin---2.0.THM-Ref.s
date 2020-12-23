%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8QAeNGZjit

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:59 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 354 expanded)
%              Number of leaves         :   23 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          :  464 (4781 expanded)
%              Number of equality atoms :   35 ( 205 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X11 )
      | ( zip_tseitin_1 @ X12 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7
       != ( k1_relset_1 @ X7 @ X8 @ X9 ) )
      | ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( zip_tseitin_1 @ X9 @ X8 @ X7 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 )
      | ( X5 = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X2 ) ) )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( v1_funct_2 @ X12 @ X11 @ X10 )
      | ( X12 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,(
    ! [X11: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X11 @ k1_xboole_0 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','16'])).

thf('42',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['32','35'])).

thf('45',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('49',plain,(
    ! [X5: $i] :
      ( zip_tseitin_0 @ X5 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['23','46','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8QAeNGZjit
% 0.15/0.37  % Computer   : n025.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 16:27:36 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.37  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 121 iterations in 0.108s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.59  thf(t130_funct_2, conjecture,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.36/0.59         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.59           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.59        ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.59            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.36/0.59            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.59              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(d1_funct_2, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_2, axiom,
% 0.36/0.59    (![C:$i,B:$i,A:$i]:
% 0.36/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_4, axiom,
% 0.36/0.59    (![B:$i,A:$i]:
% 0.36/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.59  thf(zf_stmt_5, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.59         (~ (zip_tseitin_0 @ X10 @ X11)
% 0.36/0.59          | (zip_tseitin_1 @ X12 @ X10 @ X11)
% 0.36/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10))))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.59  thf('3', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.59         (((X7) != (k1_relset_1 @ X7 @ X8 @ X9))
% 0.36/0.59          | (v1_funct_2 @ X9 @ X7 @ X8)
% 0.36/0.59          | ~ (zip_tseitin_1 @ X9 @ X8 @ X7))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      ((((sk_A) != (sk_A))
% 0.36/0.59        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.36/0.59        | (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      (((v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.59        | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.36/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.59        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.59        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.36/0.59         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.59      inference('split', [status(esa)], ['7'])).
% 0.36/0.59  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('10', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.36/0.59      inference('split', [status(esa)], ['7'])).
% 0.36/0.59  thf('11', plain, (((v1_funct_1 @ sk_C))),
% 0.36/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.36/0.59         <= (~
% 0.36/0.59             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.36/0.59      inference('split', [status(esa)], ['7'])).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.36/0.59       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.36/0.59       ~ ((v1_funct_1 @ sk_C))),
% 0.36/0.59      inference('split', [status(esa)], ['7'])).
% 0.36/0.59  thf('16', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.59      inference('sat_resolution*', [status(thm)], ['11', '14', '15'])).
% 0.36/0.59  thf('17', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['8', '16'])).
% 0.36/0.59  thf('18', plain, (~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['6', '17'])).
% 0.36/0.59  thf('19', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['2', '18'])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (![X5 : $i, X6 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X5 @ X6) | ((X5) = (k1_xboole_0)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.59  thf('21', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['2', '18'])).
% 0.36/0.59  thf('22', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.59  thf('23', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.36/0.59      inference('demod', [status(thm)], ['19', '22'])).
% 0.36/0.59  thf('24', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('25', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.36/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(cc4_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.59       ( ![C:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.59           ( v1_xboole_0 @ C ) ) ) ))).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ X2)
% 0.36/0.59          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 0.36/0.59          | (v1_xboole_0 @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.36/0.59  thf('29', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.59  thf('30', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.59  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.59  thf('32', plain, ((v1_xboole_0 @ sk_C)),
% 0.36/0.59      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.36/0.59  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.59  thf(t8_boole, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t8_boole])).
% 0.36/0.59  thf('35', plain,
% 0.36/0.59      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.59  thf('36', plain, (((k1_xboole_0) = (sk_C))),
% 0.36/0.59      inference('sup-', [status(thm)], ['32', '35'])).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.36/0.59      inference('demod', [status(thm)], ['26', '36'])).
% 0.36/0.59  thf('38', plain,
% 0.36/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.59         (((X10) != (k1_xboole_0))
% 0.36/0.59          | ((X11) = (k1_xboole_0))
% 0.36/0.59          | (v1_funct_2 @ X12 @ X11 @ X10)
% 0.36/0.59          | ((X12) != (k1_xboole_0))
% 0.36/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10))))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      (![X11 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.36/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ k1_xboole_0)))
% 0.36/0.59          | (v1_funct_2 @ k1_xboole_0 @ X11 @ k1_xboole_0)
% 0.36/0.59          | ((X11) = (k1_xboole_0)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      ((((sk_A) = (k1_xboole_0))
% 0.36/0.59        | (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['37', '39'])).
% 0.36/0.59  thf('41', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['8', '16'])).
% 0.36/0.59  thf('42', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.59  thf('43', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0)),
% 0.36/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.59  thf('44', plain, (((k1_xboole_0) = (sk_C))),
% 0.36/0.59      inference('sup-', [status(thm)], ['32', '35'])).
% 0.36/0.59  thf('45', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.36/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.59  thf('46', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.59      inference('clc', [status(thm)], ['40', '45'])).
% 0.36/0.59  thf('47', plain,
% 0.36/0.59      (![X5 : $i, X6 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X5 @ X6) | ((X5) = (k1_xboole_0)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.59  thf('48', plain,
% 0.36/0.59      (![X5 : $i, X6 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X5 @ X6) | ((X6) != (k1_xboole_0)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.59  thf('49', plain, (![X5 : $i]: (zip_tseitin_0 @ X5 @ k1_xboole_0)),
% 0.36/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.36/0.59  thf('50', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.36/0.59      inference('sup+', [status(thm)], ['47', '49'])).
% 0.36/0.59  thf('51', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.36/0.59      inference('eq_fact', [status(thm)], ['50'])).
% 0.36/0.59  thf('52', plain, ($false),
% 0.36/0.59      inference('demod', [status(thm)], ['23', '46', '51'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
