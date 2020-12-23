%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rh6SRlPPPz

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  84 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  356 ( 567 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t162_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X23: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k9_relat_1 @ X10 @ ( k9_relat_1 @ X11 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_B )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('30',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('31',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rh6SRlPPPz
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:50:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 29 iterations in 0.018s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(t162_funct_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46          ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t162_funct_1])).
% 0.21/0.46  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t2_subset, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]:
% 0.21/0.46         ((r2_hidden @ X6 @ X7)
% 0.21/0.46          | (v1_xboole_0 @ X7)
% 0.21/0.46          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.46        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf(fc1_subset_1, axiom,
% 0.21/0.46    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.46  thf('3', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.46  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.46      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf(d1_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X3 @ X2)
% 0.21/0.46          | (r1_tarski @ X3 @ X1)
% 0.21/0.46          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]:
% 0.21/0.46         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.46  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.46  thf(t71_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.46  thf('8', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.21/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.46  thf(t79_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.46         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X20 : $i, X21 : $i]:
% 0.21/0.46         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.21/0.46          | ((k5_relat_1 @ X20 @ (k6_relat_1 @ X21)) = (X20))
% 0.21/0.46          | ~ (v1_relat_1 @ X20))),
% 0.21/0.46      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.46          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.21/0.46              = (k6_relat_1 @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf(fc24_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.46       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.46  thf('11', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.46          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.21/0.46              = (k6_relat_1 @ X0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.21/0.46         = (k6_relat_1 @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.46  thf('14', plain, (![X23 : $i]: (v4_relat_1 @ (k6_relat_1 @ X23) @ X23)),
% 0.21/0.46      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.46  thf(t209_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.46       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X13 : $i, X14 : $i]:
% 0.21/0.46         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.21/0.46          | ~ (v4_relat_1 @ X13 @ X14)
% 0.21/0.46          | ~ (v1_relat_1 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.47          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf(t148_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.21/0.47          | ~ (v1_relat_1 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k2_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.47            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf('22', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.47  thf(t159_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ C ) =>
% 0.21/0.47           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.47             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X10)
% 0.21/0.47          | ((k9_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 0.21/0.47              = (k9_relat_1 @ X10 @ (k9_relat_1 @ X11 @ X12)))
% 0.21/0.47          | ~ (v1_relat_1 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.21/0.47            = (k9_relat_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.21/0.47            = (k9_relat_1 @ X1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      ((((k9_relat_1 @ (k6_relat_1 @ sk_B) @ sk_B)
% 0.21/0.47          = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.21/0.47        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['13', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.47  thf('30', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.47  thf('31', plain, (((sk_B) = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.47  thf('32', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('33', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
