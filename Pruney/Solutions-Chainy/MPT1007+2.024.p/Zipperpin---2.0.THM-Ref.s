%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RUqUOjoau

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:18 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   66 (  80 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  418 ( 726 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','13','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k1_tarski @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X7 ) @ X9 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_C @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RUqUOjoau
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:40:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 66 iterations in 0.081s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.53  thf(t61_funct_2, conjecture,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.53         ( m1_subset_1 @
% 0.36/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.53         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.53            ( m1_subset_1 @
% 0.36/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.53            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.36/0.53  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(cc2_relset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.53         ((v5_relat_1 @ X13 @ X15)
% 0.36/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.53  thf('3', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.36/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.53  thf('4', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(d1_funct_2, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_1, axiom,
% 0.36/0.53    (![C:$i,B:$i,A:$i]:
% 0.36/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.53  thf('5', plain,
% 0.36/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.53         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.36/0.53          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.36/0.53          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.53  thf('6', plain,
% 0.36/0.53      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.36/0.53        | ((k1_tarski @ sk_A)
% 0.36/0.53            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.53  thf(zf_stmt_2, axiom,
% 0.36/0.53    (![B:$i,A:$i]:
% 0.36/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.53  thf('7', plain,
% 0.36/0.53      (![X19 : $i, X20 : $i]:
% 0.36/0.53         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.53  thf('8', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.53  thf(zf_stmt_5, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.53  thf('9', plain,
% 0.36/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.53         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.36/0.53          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.36/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.36/0.53        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.53  thf('11', plain,
% 0.36/0.53      ((((sk_B) = (k1_xboole_0))
% 0.36/0.53        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['7', '10'])).
% 0.36/0.53  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('13', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.36/0.53      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.36/0.53  thf('14', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.53  thf('15', plain,
% 0.36/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.53         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.36/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.36/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.53  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.36/0.53      inference('demod', [status(thm)], ['6', '13', '16'])).
% 0.36/0.53  thf(d10_xboole_0, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.53  thf('18', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.53  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.36/0.53  thf(l1_zfmisc_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      (![X4 : $i, X5 : $i]:
% 0.36/0.53         ((r2_hidden @ X4 @ X5) | ~ (r1_tarski @ (k1_tarski @ X4) @ X5))),
% 0.36/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.53  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.53  thf('22', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.36/0.53      inference('sup+', [status(thm)], ['17', '21'])).
% 0.36/0.53  thf(t172_funct_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.53       ( ![C:$i]:
% 0.36/0.53         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.53           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.36/0.53  thf('23', plain,
% 0.36/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X7 @ (k1_relat_1 @ X8))
% 0.36/0.53          | (r2_hidden @ (k1_funct_1 @ X8 @ X7) @ X9)
% 0.36/0.53          | ~ (v1_funct_1 @ X8)
% 0.36/0.53          | ~ (v5_relat_1 @ X8 @ X9)
% 0.36/0.53          | ~ (v1_relat_1 @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.36/0.53  thf('24', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v1_relat_1 @ sk_C)
% 0.36/0.53          | ~ (v5_relat_1 @ sk_C @ X0)
% 0.36/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ 
% 0.36/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(cc1_relset_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.53       ( v1_relat_1 @ C ) ))).
% 0.36/0.53  thf('26', plain,
% 0.36/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.53         ((v1_relat_1 @ X10)
% 0.36/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.53  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.53  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('29', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v5_relat_1 @ sk_C @ X0)
% 0.36/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ X0))),
% 0.36/0.53      inference('demod', [status(thm)], ['24', '27', '28'])).
% 0.36/0.53  thf('30', plain, ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)),
% 0.36/0.53      inference('sup-', [status(thm)], ['3', '29'])).
% 0.36/0.53  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
