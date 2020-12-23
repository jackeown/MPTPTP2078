%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AOnntYPXIl

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:40 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   51 (  63 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  246 ( 390 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['2','3'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X12 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( ( k6_domain_1 @ X24 @ X25 )
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('13',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(fc3_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_subset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    $false ),
    inference('sup-',[status(thm)],['19','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AOnntYPXIl
% 0.15/0.37  % Computer   : n023.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:47:36 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 33 iterations in 0.017s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.24/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.51  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.24/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.24/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.24/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.24/0.51  thf(t6_tex_2, conjecture,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( m1_subset_1 @ B @ A ) =>
% 0.24/0.51           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.24/0.51                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i]:
% 0.24/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.51          ( ![B:$i]:
% 0.24/0.51            ( ( m1_subset_1 @ B @ A ) =>
% 0.24/0.51              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.24/0.51                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.24/0.51  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t2_subset, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.24/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X17 : $i, X18 : $i]:
% 0.24/0.51         ((r2_hidden @ X17 @ X18)
% 0.24/0.51          | (v1_xboole_0 @ X18)
% 0.24/0.51          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.24/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.24/0.51  thf('2', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.51  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('4', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.24/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.24/0.51  thf(t63_subset_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.24/0.51       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X12 : $i, X13 : $i]:
% 0.24/0.51         ((m1_subset_1 @ (k1_tarski @ X12) @ (k1_zfmisc_1 @ X13))
% 0.24/0.51          | ~ (r2_hidden @ X12 @ X13))),
% 0.24/0.51      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.24/0.51  thf('6', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.51  thf(cc2_tex_2, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.51           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (![X26 : $i, X27 : $i]:
% 0.24/0.51         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.24/0.51          | ~ (v1_subset_1 @ X26 @ X27)
% 0.24/0.51          | (v1_xboole_0 @ X26)
% 0.24/0.51          | ~ (v1_zfmisc_1 @ X27)
% 0.24/0.51          | (v1_xboole_0 @ X27))),
% 0.24/0.51      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (((v1_xboole_0 @ sk_A)
% 0.24/0.51        | ~ (v1_zfmisc_1 @ sk_A)
% 0.24/0.51        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.24/0.51        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.51  thf('9', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('10', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('11', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X24 : $i, X25 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ X24)
% 0.24/0.51          | ~ (m1_subset_1 @ X25 @ X24)
% 0.24/0.51          | ((k6_domain_1 @ X24 @ X25) = (k1_tarski @ X25)))),
% 0.24/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.24/0.51        | (v1_xboole_0 @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.51  thf('14', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.24/0.51      inference('clc', [status(thm)], ['13', '14'])).
% 0.24/0.51  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.24/0.51      inference('demod', [status(thm)], ['10', '15'])).
% 0.24/0.51  thf('17', plain,
% 0.24/0.51      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.24/0.51      inference('demod', [status(thm)], ['8', '9', '16'])).
% 0.24/0.51  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.24/0.51      inference('clc', [status(thm)], ['17', '18'])).
% 0.24/0.51  thf(t69_enumset1, axiom,
% 0.24/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.51  thf('20', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.51  thf(t70_enumset1, axiom,
% 0.24/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.24/0.51  thf('21', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i]:
% 0.24/0.51         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.24/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.24/0.51  thf(t71_enumset1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.24/0.51  thf('22', plain,
% 0.24/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.51         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.24/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.24/0.51  thf(fc3_subset_1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.51     ( ~( v1_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) ) ))).
% 0.24/0.51  thf('23', plain,
% 0.24/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.51         ~ (v1_xboole_0 @ (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.24/0.51      inference('cnf', [status(esa)], [fc3_subset_1])).
% 0.24/0.51  thf('24', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.24/0.51  thf('25', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['21', '24'])).
% 0.24/0.51  thf('26', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['20', '25'])).
% 0.24/0.51  thf('27', plain, ($false), inference('sup-', [status(thm)], ['19', '26'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
