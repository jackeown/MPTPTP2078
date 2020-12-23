%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.le4GdYFJg5

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:35 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   65 (  84 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  392 ( 654 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t36_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_relset_1])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k6_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( k6_relset_1 @ X32 @ X33 @ X30 @ X31 )
        = ( k8_relat_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v5_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['8','13'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X12 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('20',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('25',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['23','25'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( ( k8_relat_1 @ X26 @ X25 )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k8_relat_1 @ sk_C_2 @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('30',plain,
    ( ( k8_relat_1 @ sk_C_2 @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['0','3','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('33',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_relset_1 @ X34 @ X35 @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['33'])).

thf('35',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['31','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.le4GdYFJg5
% 0.14/0.38  % Computer   : n007.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 14:10:06 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 228 iterations in 0.109s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.60  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.38/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(t36_relset_1, conjecture,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( r1_tarski @ B @ C ) =>
% 0.38/0.60         ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60          ( ( r1_tarski @ B @ C ) =>
% 0.38/0.60            ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t36_relset_1])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.60          (k6_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D) @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k6_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.60         (((k6_relset_1 @ X32 @ X33 @ X30 @ X31) = (k8_relat_1 @ X30 @ X31))
% 0.38/0.60          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         ((v5_relat_1 @ X27 @ X29)
% 0.38/0.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.60  thf('6', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.38/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.60  thf(d19_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X21 : $i, X22 : $i]:
% 0.38/0.60         (~ (v5_relat_1 @ X21 @ X22)
% 0.38/0.60          | (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 0.38/0.60          | ~ (v1_relat_1 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X19 : $i, X20 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.38/0.60          | (v1_relat_1 @ X19)
% 0.38/0.60          | ~ (v1_relat_1 @ X20))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.60  thf(fc6_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.60  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.60  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.38/0.60      inference('demod', [status(thm)], ['8', '13'])).
% 0.38/0.60  thf(d1_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.38/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X4 @ X5)
% 0.38/0.60          | (r2_hidden @ X4 @ X6)
% 0.38/0.60          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X4 : $i, X5 : $i]:
% 0.38/0.60         ((r2_hidden @ X4 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X4 @ X5))),
% 0.38/0.60      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.60  thf('17', plain, ((r2_hidden @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '16'])).
% 0.38/0.60  thf('18', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t79_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.60       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (![X12 : $i, X13 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_zfmisc_1 @ X12) @ (k1_zfmisc_1 @ X13))
% 0.38/0.60          | ~ (r1_tarski @ X12 @ X13))),
% 0.38/0.60      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      ((r1_tarski @ (k1_zfmisc_1 @ sk_B) @ (k1_zfmisc_1 @ sk_C_2))),
% 0.38/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.60  thf(d3_tarski, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.60          | (r2_hidden @ X0 @ X2)
% 0.38/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_C_2))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      ((r2_hidden @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_C_2))),
% 0.38/0.60      inference('sup-', [status(thm)], ['17', '22'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X7 @ X6)
% 0.38/0.60          | (r1_tarski @ X7 @ X5)
% 0.38/0.60          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X5 : $i, X7 : $i]:
% 0.38/0.60         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.60  thf('26', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_2)),
% 0.38/0.60      inference('sup-', [status(thm)], ['23', '25'])).
% 0.38/0.60  thf(t125_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ B ) =>
% 0.38/0.60       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.38/0.60         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (![X25 : $i, X26 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.38/0.60          | ((k8_relat_1 @ X26 @ X25) = (X25))
% 0.38/0.60          | ~ (v1_relat_1 @ X25))),
% 0.38/0.60      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ sk_D) | ((k8_relat_1 @ sk_C_2 @ sk_D) = (sk_D)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.60  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.60  thf('30', plain, (((k8_relat_1 @ sk_C_2 @ sk_D) = (sk_D))),
% 0.38/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.60  thf('31', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '3', '30'])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(reflexivity_r2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.38/0.60         ((r2_relset_1 @ X34 @ X35 @ X36 @ X36)
% 0.38/0.60          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.38/0.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.38/0.60      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.38/0.60      inference('condensation', [status(thm)], ['33'])).
% 0.38/0.60  thf('35', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.38/0.60      inference('sup-', [status(thm)], ['32', '34'])).
% 0.38/0.60  thf('36', plain, ($false), inference('demod', [status(thm)], ['31', '35'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
