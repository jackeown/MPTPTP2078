%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.onsRVaBO31

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:18 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   65 (  89 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  453 ( 778 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ~ ( r2_hidden @ C @ B )
                 => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ X51 )
      | ( r2_hidden @ X50 @ X51 )
      | ( v1_xboole_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X12 ) )
      | ( r2_hidden @ X9 @ X12 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k3_tarski @ ( k2_tarski @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('15',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k3_subset_1 @ X53 @ X54 )
        = ( k4_xboole_0 @ X53 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.onsRVaBO31
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:09:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.60/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.77  % Solved by: fo/fo7.sh
% 0.60/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.77  % done 707 iterations in 0.326s
% 0.60/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.77  % SZS output start Refutation
% 0.60/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.77  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.60/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.77  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.60/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.77  thf(t100_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.60/0.77  thf('0', plain,
% 0.60/0.77      (![X13 : $i, X14 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X13 @ X14)
% 0.60/0.77           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.77  thf(t50_subset_1, conjecture,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.60/0.77       ( ![B:$i]:
% 0.60/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.77           ( ![C:$i]:
% 0.60/0.77             ( ( m1_subset_1 @ C @ A ) =>
% 0.60/0.77               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.60/0.77                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.60/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.77    (~( ![A:$i]:
% 0.60/0.77        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.60/0.77          ( ![B:$i]:
% 0.60/0.77            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.77              ( ![C:$i]:
% 0.60/0.77                ( ( m1_subset_1 @ C @ A ) =>
% 0.60/0.77                  ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.60/0.77                    ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.60/0.77    inference('cnf.neg', [status(esa)], [t50_subset_1])).
% 0.60/0.77  thf('1', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(d2_subset_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( ( v1_xboole_0 @ A ) =>
% 0.60/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.60/0.77       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.60/0.77  thf('2', plain,
% 0.60/0.77      (![X50 : $i, X51 : $i]:
% 0.60/0.77         (~ (m1_subset_1 @ X50 @ X51)
% 0.60/0.77          | (r2_hidden @ X50 @ X51)
% 0.60/0.77          | (v1_xboole_0 @ X51))),
% 0.60/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.77  thf('3', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.77  thf(t1_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.60/0.77       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.60/0.77  thf('4', plain,
% 0.60/0.77      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.60/0.77         ((r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X12))
% 0.60/0.77          | (r2_hidden @ X9 @ X12)
% 0.60/0.77          | ~ (r2_hidden @ X9 @ X10))),
% 0.60/0.77      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.60/0.77  thf('5', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ sk_A)
% 0.60/0.77          | (r2_hidden @ sk_C @ X0)
% 0.60/0.77          | (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.77  thf('6', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.60/0.77          | (r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 0.60/0.77          | (v1_xboole_0 @ sk_A))),
% 0.60/0.77      inference('sup+', [status(thm)], ['0', '5'])).
% 0.60/0.77  thf('7', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ sk_A)
% 0.60/0.77          | (r2_hidden @ sk_C @ X0)
% 0.60/0.77          | (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.77  thf('8', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.77  thf(d3_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.60/0.77       ( ![D:$i]:
% 0.60/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.77           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.60/0.77  thf('9', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X0 @ X3)
% 0.60/0.77          | (r2_hidden @ X0 @ X2)
% 0.60/0.77          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.60/0.77      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.60/0.77  thf('10', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.60/0.77         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.60/0.77      inference('simplify', [status(thm)], ['9'])).
% 0.60/0.77  thf(l51_zfmisc_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.60/0.77  thf('11', plain,
% 0.60/0.77      (![X48 : $i, X49 : $i]:
% 0.60/0.77         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 0.60/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.60/0.77  thf('12', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.60/0.77         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.60/0.77          | ~ (r2_hidden @ X0 @ X3))),
% 0.60/0.77      inference('demod', [status(thm)], ['10', '11'])).
% 0.60/0.77  thf('13', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ sk_A)
% 0.60/0.77          | (r2_hidden @ sk_C @ (k3_tarski @ (k2_tarski @ sk_A @ X0))))),
% 0.60/0.77      inference('sup-', [status(thm)], ['8', '12'])).
% 0.60/0.77  thf(t95_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( k3_xboole_0 @ A @ B ) =
% 0.60/0.77       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.60/0.77  thf('14', plain,
% 0.60/0.77      (![X19 : $i, X20 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X19 @ X20)
% 0.60/0.77           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.60/0.77              (k2_xboole_0 @ X19 @ X20)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.60/0.77  thf('15', plain,
% 0.60/0.77      (![X48 : $i, X49 : $i]:
% 0.60/0.77         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 0.60/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.60/0.77  thf(t91_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.60/0.77       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.60/0.77  thf('16', plain,
% 0.60/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.60/0.77           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.60/0.77  thf('17', plain,
% 0.60/0.77      (![X19 : $i, X20 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X19 @ X20)
% 0.60/0.77           = (k5_xboole_0 @ X19 @ 
% 0.60/0.77              (k5_xboole_0 @ X20 @ (k3_tarski @ (k2_tarski @ X19 @ X20)))))),
% 0.60/0.77      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.60/0.77  thf('18', plain,
% 0.60/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.60/0.77           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.60/0.77  thf('19', plain,
% 0.60/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X9 @ X10)
% 0.60/0.77          | ~ (r2_hidden @ X9 @ X11)
% 0.60/0.77          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.60/0.77  thf('20', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 0.60/0.77          | ~ (r2_hidden @ X3 @ X0)
% 0.60/0.77          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X2 @ X1)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.77  thf('21', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.77         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.60/0.77          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.60/0.77          | ~ (r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.60/0.77      inference('sup-', [status(thm)], ['17', '20'])).
% 0.60/0.77  thf('22', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ sk_A)
% 0.60/0.77          | ~ (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0))
% 0.60/0.77          | ~ (r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['13', '21'])).
% 0.60/0.77  thf('23', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ sk_C @ X0)
% 0.60/0.77          | (v1_xboole_0 @ sk_A)
% 0.60/0.77          | ~ (r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 0.60/0.77          | (v1_xboole_0 @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['7', '22'])).
% 0.60/0.77  thf('24', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 0.60/0.77          | (v1_xboole_0 @ sk_A)
% 0.60/0.77          | (r2_hidden @ sk_C @ X0))),
% 0.60/0.77      inference('simplify', [status(thm)], ['23'])).
% 0.60/0.77  thf('25', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v1_xboole_0 @ sk_A)
% 0.60/0.77          | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.60/0.77          | (r2_hidden @ sk_C @ X0)
% 0.60/0.77          | (v1_xboole_0 @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['6', '24'])).
% 0.60/0.77  thf('26', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((r2_hidden @ sk_C @ X0)
% 0.60/0.77          | (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.60/0.77          | (v1_xboole_0 @ sk_A))),
% 0.60/0.77      inference('simplify', [status(thm)], ['25'])).
% 0.60/0.77  thf('27', plain, (~ (r2_hidden @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(d5_subset_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.77       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.60/0.77  thf('29', plain,
% 0.60/0.77      (![X53 : $i, X54 : $i]:
% 0.60/0.77         (((k3_subset_1 @ X53 @ X54) = (k4_xboole_0 @ X53 @ X54))
% 0.60/0.77          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X53)))),
% 0.60/0.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.60/0.77  thf('30', plain,
% 0.60/0.77      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.77  thf('31', plain, (~ (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.77      inference('demod', [status(thm)], ['27', '30'])).
% 0.60/0.77  thf('32', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_B))),
% 0.60/0.77      inference('sup-', [status(thm)], ['26', '31'])).
% 0.60/0.77  thf('33', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('34', plain, ((v1_xboole_0 @ sk_A)),
% 0.60/0.77      inference('clc', [status(thm)], ['32', '33'])).
% 0.60/0.77  thf(l13_xboole_0, axiom,
% 0.60/0.77    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.77  thf('35', plain,
% 0.60/0.77      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.60/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.77  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['34', '35'])).
% 0.60/0.77  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('38', plain, ($false),
% 0.60/0.77      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.60/0.77  
% 0.60/0.77  % SZS output end Refutation
% 0.60/0.77  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
