%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rZthH6wZXa

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:07 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   69 (  82 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  489 ( 680 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('5',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X25 ) @ X24 )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('7',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k9_relat_1 @ X19 @ X20 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X19 ) @ X20 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('9',plain,
    ( ( sk_A
      = ( k10_relat_1 @ ( k2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X26 ) )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X16: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('14',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ C ) )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k10_relat_1 @ X22 @ X23 ) @ ( k10_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) @ ( k9_relat_1 @ X21 @ X23 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t160_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( r1_tarski @ ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('30',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rZthH6wZXa
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 133 iterations in 0.111s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.57  thf(t164_funct_1, conjecture,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.57       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.40/0.57         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i,B:$i]:
% 0.40/0.57        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.57          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.40/0.57            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.40/0.57  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(d1_zfmisc_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.40/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.40/0.57          | (r2_hidden @ X3 @ X5)
% 0.40/0.57          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.57  thf('2', plain,
% 0.40/0.57      (![X3 : $i, X4 : $i]:
% 0.40/0.57         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.40/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.40/0.57  thf('3', plain, ((r2_hidden @ sk_A @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['0', '2'])).
% 0.40/0.57  thf(t1_subset, axiom,
% 0.40/0.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.40/0.57  thf('4', plain,
% 0.40/0.57      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.40/0.57      inference('cnf', [status(esa)], [t1_subset])).
% 0.40/0.57  thf('5', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.57  thf(t162_funct_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.40/0.57  thf('6', plain,
% 0.40/0.57      (![X24 : $i, X25 : $i]:
% 0.40/0.57         (((k9_relat_1 @ (k6_relat_1 @ X25) @ X24) = (X24))
% 0.40/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      (((k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.57  thf(t154_funct_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.57       ( ( v2_funct_1 @ B ) =>
% 0.40/0.57         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      (![X19 : $i, X20 : $i]:
% 0.40/0.57         (~ (v2_funct_1 @ X19)
% 0.40/0.57          | ((k9_relat_1 @ X19 @ X20)
% 0.40/0.57              = (k10_relat_1 @ (k2_funct_1 @ X19) @ X20))
% 0.40/0.57          | ~ (v1_funct_1 @ X19)
% 0.40/0.57          | ~ (v1_relat_1 @ X19))),
% 0.40/0.57      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.40/0.57  thf('9', plain,
% 0.40/0.57      ((((sk_A)
% 0.40/0.57          = (k10_relat_1 @ (k2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) @ 
% 0.40/0.57             sk_A))
% 0.40/0.57        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.40/0.57        | ~ (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.40/0.57        | ~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 0.40/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.40/0.57  thf(t67_funct_1, axiom,
% 0.40/0.57    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.40/0.57  thf('10', plain,
% 0.40/0.57      (![X26 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X26)) = (k6_relat_1 @ X26))),
% 0.40/0.57      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.40/0.57  thf(fc3_funct_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.40/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.40/0.57  thf('11', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.40/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.40/0.57  thf('12', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 0.40/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.40/0.57  thf(fc4_funct_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.40/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.40/0.57  thf('13', plain, (![X16 : $i]: (v2_funct_1 @ (k6_relat_1 @ X16))),
% 0.40/0.57      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (((sk_A) = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.40/0.57  thf(t78_relat_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( v1_relat_1 @ A ) =>
% 0.40/0.57       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.40/0.57  thf('15', plain,
% 0.40/0.57      (![X12 : $i]:
% 0.40/0.57         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X12)) @ X12) = (X12))
% 0.40/0.57          | ~ (v1_relat_1 @ X12))),
% 0.40/0.57      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.40/0.57  thf(d10_xboole_0, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.57  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.57  thf(t71_relat_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.40/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.40/0.57  thf('18', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.40/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.40/0.57  thf(t160_funct_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( v1_relat_1 @ B ) =>
% 0.40/0.57       ( ![C:$i]:
% 0.40/0.57         ( ( v1_relat_1 @ C ) =>
% 0.40/0.57           ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ C ) ) =>
% 0.40/0.57             ( r1_tarski @
% 0.40/0.57               ( k10_relat_1 @ B @ A ) @ 
% 0.40/0.57               ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) ))).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X21)
% 0.40/0.57          | (r1_tarski @ (k10_relat_1 @ X22 @ X23) @ 
% 0.40/0.57             (k10_relat_1 @ (k5_relat_1 @ X22 @ X21) @ (k9_relat_1 @ X21 @ X23)))
% 0.40/0.57          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ (k1_relat_1 @ X21))
% 0.40/0.57          | ~ (v1_relat_1 @ X22))),
% 0.40/0.57      inference('cnf', [status(esa)], [t160_funct_1])).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.40/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.40/0.57          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.40/0.57             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.40/0.57              (k9_relat_1 @ X1 @ X2)))
% 0.40/0.57          | ~ (v1_relat_1 @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.57  thf('21', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.40/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.40/0.57  thf('22', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.40/0.57          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.40/0.57             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 0.40/0.57              (k9_relat_1 @ X1 @ X2)))
% 0.40/0.57          | ~ (v1_relat_1 @ X1))),
% 0.40/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.57  thf('23', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | (r1_tarski @ 
% 0.40/0.57             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1) @ 
% 0.40/0.57             (k10_relat_1 @ 
% 0.40/0.57              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 0.40/0.57              (k9_relat_1 @ X0 @ X1))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['17', '22'])).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1) @ 
% 0.40/0.57           (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)))
% 0.40/0.57          | ~ (v1_relat_1 @ X0)
% 0.40/0.57          | ~ (v1_relat_1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['15', '23'])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X0)
% 0.40/0.57          | (r1_tarski @ 
% 0.40/0.57             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1) @ 
% 0.40/0.57             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1))))),
% 0.40/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.57  thf('26', plain,
% 0.40/0.57      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.40/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.57      inference('sup+', [status(thm)], ['14', '25'])).
% 0.40/0.57  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('28', plain,
% 0.40/0.57      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.57  thf(t152_funct_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.57       ( ( v2_funct_1 @ B ) =>
% 0.40/0.57         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      (![X17 : $i, X18 : $i]:
% 0.40/0.57         (~ (v2_funct_1 @ X17)
% 0.40/0.57          | (r1_tarski @ (k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X18)) @ X18)
% 0.40/0.57          | ~ (v1_funct_1 @ X17)
% 0.40/0.57          | ~ (v1_relat_1 @ X17))),
% 0.40/0.57      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.40/0.57  thf('30', plain,
% 0.40/0.57      (![X0 : $i, X2 : $i]:
% 0.40/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.57  thf('31', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ X1)
% 0.40/0.57          | ~ (v1_funct_1 @ X1)
% 0.40/0.57          | ~ (v2_funct_1 @ X1)
% 0.40/0.57          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.40/0.57          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.57  thf('32', plain,
% 0.40/0.57      ((((sk_A) = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.40/0.57        | ~ (v2_funct_1 @ sk_B)
% 0.40/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.40/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.57      inference('sup-', [status(thm)], ['28', '31'])).
% 0.40/0.57  thf('33', plain, ((v2_funct_1 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('36', plain,
% 0.40/0.57      (((sk_A) = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.40/0.57  thf('37', plain,
% 0.40/0.57      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('38', plain, ($false),
% 0.40/0.57      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
