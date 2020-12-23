%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5hfdwJWVnl

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 101 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  325 ( 901 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t176_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v5_relat_1 @ C @ A )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
         => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_funct_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ( ( k8_relat_1 @ X5 @ X4 )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k8_relat_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k8_relat_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf(t85_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_relat_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_relat_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) )
              & ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) )
        & ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
       => ( ( k1_funct_1 @ B @ D )
          = ( k1_funct_1 @ C @ D ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( zip_tseitin_1 @ D @ C @ A ) )
              & ! [D: $i] :
                  ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17
       != ( k8_relat_1 @ X18 @ X16 ) )
      | ( zip_tseitin_1 @ X21 @ X16 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,(
    ! [X16: $i,X18: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X18 @ X16 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X18 @ X16 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ ( k8_relat_1 @ X18 @ X16 ) ) )
      | ( zip_tseitin_1 @ X21 @ X16 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( zip_tseitin_1 @ X0 @ sk_C @ sk_A )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k8_relat_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k8_relat_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ X0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17','18','19'])).

thf('21',plain,(
    zip_tseitin_1 @ sk_B @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X13 @ X12 ) @ X14 )
      | ~ ( zip_tseitin_1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5hfdwJWVnl
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 50 iterations in 0.033s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.47  thf(t176_funct_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.47       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.21/0.47         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.47          ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.21/0.47            ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t176_funct_1])).
% 0.21/0.47  thf('0', plain, (~ (m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_B) @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((r2_hidden @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d19_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (v5_relat_1 @ X2 @ X3)
% 0.21/0.47          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.21/0.47          | ~ (v1_relat_1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(t125_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.47         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.21/0.47          | ((k8_relat_1 @ X5 @ X4) = (X4))
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ sk_C) | ((k8_relat_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, (((k8_relat_1 @ sk_A @ sk_C) = (sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(t85_funct_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.21/0.47           ( ( ( B ) = ( k8_relat_1 @ A @ C ) ) <=>
% 0.21/0.47             ( ( ![D:$i]:
% 0.21/0.47                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.47                   ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) & 
% 0.21/0.47               ( ![D:$i]:
% 0.21/0.47                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.47                   ( ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) & 
% 0.21/0.47                     ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_2, axiom,
% 0.21/0.47    (![D:$i,C:$i,A:$i]:
% 0.21/0.47     ( ( zip_tseitin_1 @ D @ C @ A ) <=>
% 0.21/0.47       ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.47         ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) ) ))).
% 0.21/0.47  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_4, axiom,
% 0.21/0.47    (![D:$i,C:$i,B:$i]:
% 0.21/0.47     ( ( zip_tseitin_0 @ D @ C @ B ) <=>
% 0.21/0.47       ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.47         ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_5, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.47           ( ( ( B ) = ( k8_relat_1 @ A @ C ) ) <=>
% 0.21/0.47             ( ( ![D:$i]:
% 0.21/0.47                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.47                   ( zip_tseitin_1 @ D @ C @ A ) ) ) & 
% 0.21/0.47               ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X16 : $i, X17 : $i, X18 : $i, X21 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X16)
% 0.21/0.47          | ~ (v1_funct_1 @ X16)
% 0.21/0.47          | ((X17) != (k8_relat_1 @ X18 @ X16))
% 0.21/0.47          | (zip_tseitin_1 @ X21 @ X16 @ X18)
% 0.21/0.47          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X17))
% 0.21/0.47          | ~ (v1_funct_1 @ X17)
% 0.21/0.47          | ~ (v1_relat_1 @ X17))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X16 : $i, X18 : $i, X21 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (k8_relat_1 @ X18 @ X16))
% 0.21/0.47          | ~ (v1_funct_1 @ (k8_relat_1 @ X18 @ X16))
% 0.21/0.47          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ (k8_relat_1 @ X18 @ X16)))
% 0.21/0.47          | (zip_tseitin_1 @ X21 @ X16 @ X18)
% 0.21/0.47          | ~ (v1_funct_1 @ X16)
% 0.21/0.47          | ~ (v1_relat_1 @ X16))),
% 0.21/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C))
% 0.21/0.47          | ~ (v1_relat_1 @ sk_C)
% 0.21/0.47          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.47          | (zip_tseitin_1 @ X0 @ sk_C @ sk_A)
% 0.21/0.47          | ~ (v1_funct_1 @ (k8_relat_1 @ sk_A @ sk_C))
% 0.21/0.47          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.47  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, (((k8_relat_1 @ sk_A @ sk_C) = (sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain, (((k8_relat_1 @ sk_A @ sk_C) = (sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C))
% 0.21/0.47          | (zip_tseitin_1 @ X0 @ sk_C @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)],
% 0.21/0.47                ['13', '14', '15', '16', '17', '18', '19'])).
% 0.21/0.47  thf('21', plain, ((zip_tseitin_1 @ sk_B @ sk_C @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_funct_1 @ X13 @ X12) @ X14)
% 0.21/0.47          | ~ (zip_tseitin_1 @ X12 @ X13 @ X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.47  thf('23', plain, ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_B) @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf(t1_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.47  thf('25', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_B) @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
