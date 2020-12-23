%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vXkq39nQun

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:06 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  221 ( 378 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t214_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t214_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ ( k2_zfmisc_1 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ X1 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vXkq39nQun
% 0.11/0.30  % Computer   : n014.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 14:09:37 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  % Running portfolio for 600 s
% 0.11/0.30  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.31  % Number of cores: 8
% 0.11/0.31  % Python version: Python 3.6.8
% 0.11/0.31  % Running in FO mode
% 0.17/0.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.17/0.40  % Solved by: fo/fo7.sh
% 0.17/0.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.40  % done 32 iterations in 0.019s
% 0.17/0.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.17/0.40  % SZS output start Refutation
% 0.17/0.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.17/0.40  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.40  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.40  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.17/0.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.17/0.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.17/0.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.17/0.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.17/0.40  thf(t214_relat_1, conjecture,
% 0.17/0.40    (![A:$i]:
% 0.17/0.40     ( ( v1_relat_1 @ A ) =>
% 0.17/0.40       ( ![B:$i]:
% 0.17/0.40         ( ( v1_relat_1 @ B ) =>
% 0.17/0.40           ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.17/0.40             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.17/0.40  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.40    (~( ![A:$i]:
% 0.17/0.40        ( ( v1_relat_1 @ A ) =>
% 0.17/0.40          ( ![B:$i]:
% 0.17/0.40            ( ( v1_relat_1 @ B ) =>
% 0.17/0.40              ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.17/0.40                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.17/0.40    inference('cnf.neg', [status(esa)], [t214_relat_1])).
% 0.17/0.40  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.17/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.40  thf('1', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.17/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.40  thf(t127_zfmisc_1, axiom,
% 0.17/0.40    (![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.40     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.17/0.40       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.17/0.40  thf('2', plain,
% 0.17/0.40      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.17/0.40         ((r1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9) @ (k2_zfmisc_1 @ X10 @ X11))
% 0.17/0.40          | ~ (r1_xboole_0 @ X8 @ X10))),
% 0.17/0.40      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.17/0.40  thf('3', plain,
% 0.17/0.40      (![X0 : $i, X1 : $i]:
% 0.17/0.40         (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ X1) @ 
% 0.17/0.40          (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ X0))),
% 0.17/0.40      inference('sup-', [status(thm)], ['1', '2'])).
% 0.17/0.40  thf(t21_relat_1, axiom,
% 0.17/0.40    (![A:$i]:
% 0.17/0.40     ( ( v1_relat_1 @ A ) =>
% 0.17/0.40       ( r1_tarski @
% 0.17/0.40         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.17/0.40  thf('4', plain,
% 0.17/0.40      (![X12 : $i]:
% 0.17/0.40         ((r1_tarski @ X12 @ 
% 0.17/0.40           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.17/0.40          | ~ (v1_relat_1 @ X12))),
% 0.17/0.40      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.17/0.40  thf(t12_xboole_1, axiom,
% 0.17/0.40    (![A:$i,B:$i]:
% 0.17/0.40     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.17/0.40  thf('5', plain,
% 0.17/0.40      (![X2 : $i, X3 : $i]:
% 0.17/0.40         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.17/0.40      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.17/0.40  thf('6', plain,
% 0.17/0.40      (![X0 : $i]:
% 0.17/0.40         (~ (v1_relat_1 @ X0)
% 0.17/0.40          | ((k2_xboole_0 @ X0 @ 
% 0.17/0.40              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.17/0.40              = (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.17/0.40      inference('sup-', [status(thm)], ['4', '5'])).
% 0.17/0.41  thf(t70_xboole_1, axiom,
% 0.17/0.41    (![A:$i,B:$i,C:$i]:
% 0.17/0.41     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.17/0.41            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.17/0.41       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.17/0.41            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.17/0.41  thf('7', plain,
% 0.17/0.41      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.17/0.41         ((r1_xboole_0 @ X4 @ X5)
% 0.17/0.41          | ~ (r1_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X7)))),
% 0.17/0.41      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.17/0.41  thf('8', plain,
% 0.17/0.41      (![X0 : $i, X1 : $i]:
% 0.17/0.41         (~ (r1_xboole_0 @ X1 @ 
% 0.17/0.41             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.17/0.41          | ~ (v1_relat_1 @ X0)
% 0.17/0.41          | (r1_xboole_0 @ X1 @ X0))),
% 0.17/0.41      inference('sup-', [status(thm)], ['6', '7'])).
% 0.17/0.41  thf('9', plain,
% 0.17/0.41      (![X0 : $i]:
% 0.17/0.41         ((r1_xboole_0 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ X0) @ sk_B)
% 0.17/0.41          | ~ (v1_relat_1 @ sk_B))),
% 0.17/0.41      inference('sup-', [status(thm)], ['3', '8'])).
% 0.17/0.41  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.17/0.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.41  thf('11', plain,
% 0.17/0.41      (![X0 : $i]:
% 0.17/0.41         (r1_xboole_0 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ X0) @ sk_B)),
% 0.17/0.41      inference('demod', [status(thm)], ['9', '10'])).
% 0.17/0.41  thf(symmetry_r1_xboole_0, axiom,
% 0.17/0.41    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.17/0.41  thf('12', plain,
% 0.17/0.41      (![X0 : $i, X1 : $i]:
% 0.17/0.41         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.17/0.41      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.17/0.41  thf('13', plain,
% 0.17/0.41      (![X0 : $i]:
% 0.17/0.41         (r1_xboole_0 @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ X0))),
% 0.17/0.41      inference('sup-', [status(thm)], ['11', '12'])).
% 0.17/0.41  thf('14', plain,
% 0.17/0.41      (![X0 : $i, X1 : $i]:
% 0.17/0.41         (~ (r1_xboole_0 @ X1 @ 
% 0.17/0.41             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.17/0.41          | ~ (v1_relat_1 @ X0)
% 0.17/0.41          | (r1_xboole_0 @ X1 @ X0))),
% 0.17/0.41      inference('sup-', [status(thm)], ['6', '7'])).
% 0.17/0.41  thf('15', plain, (((r1_xboole_0 @ sk_B @ sk_A) | ~ (v1_relat_1 @ sk_A))),
% 0.17/0.41      inference('sup-', [status(thm)], ['13', '14'])).
% 0.17/0.41  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.17/0.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.41  thf('17', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.17/0.41      inference('demod', [status(thm)], ['15', '16'])).
% 0.17/0.41  thf('18', plain,
% 0.17/0.41      (![X0 : $i, X1 : $i]:
% 0.17/0.41         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.17/0.41      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.17/0.41  thf('19', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.17/0.41      inference('sup-', [status(thm)], ['17', '18'])).
% 0.17/0.41  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.17/0.41  
% 0.17/0.41  % SZS output end Refutation
% 0.17/0.41  
% 0.17/0.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
