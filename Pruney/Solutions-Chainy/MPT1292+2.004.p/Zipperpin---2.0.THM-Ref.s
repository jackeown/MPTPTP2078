%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OYmbpbWoQL

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 (  98 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  331 ( 651 expanded)
%              Number of equality atoms :   34 (  61 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t5_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) )
              & ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) )
                & ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_tops_2])).

thf('0',plain,(
    m1_setfam_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ ( k3_tarski @ X26 ) )
      | ~ ( m1_setfam_1 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('2',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('4',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['2','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X8: $i] :
      ( r1_tarski @ sk_B_1 @ X8 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['7','12'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t140_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ ( k1_tarski @ X22 ) ) @ ( k1_tarski @ X22 ) )
        = X21 )
      | ~ ( r2_hidden @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t140_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ X21 )
        = X21 )
      | ~ ( r2_hidden @ X22 @ X21 ) ) ),
    inference(demod,[status(thm)],['21','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('34',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
     != sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['19','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OYmbpbWoQL
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:43:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 236 iterations in 0.073s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.54  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.22/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(t5_tops_2, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @
% 0.22/0.54             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.54           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.54                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( m1_subset_1 @
% 0.22/0.54                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.54              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.54                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.22/0.54  thf('0', plain, ((m1_setfam_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d12_setfam_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X25 : $i, X26 : $i]:
% 0.22/0.54         ((r1_tarski @ X25 @ (k3_tarski @ X26)) | ~ (m1_setfam_1 @ X26 @ X25))),
% 0.22/0.54      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.22/0.54  thf('2', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.54  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.54  thf('3', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.22/0.54  thf('4', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('6', plain, (((k3_tarski @ sk_B_1) = (sk_B_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.54  thf('7', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['2', '6'])).
% 0.22/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.54  thf('8', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.54  thf('9', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('10', plain, (![X8 : $i]: (r1_tarski @ sk_B_1 @ X8)),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X3 : $i, X5 : $i]:
% 0.22/0.54         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B_1) | ((X0) = (sk_B_1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '12'])).
% 0.22/0.54  thf(fc2_struct_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X30 : $i]:
% 0.22/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X30))
% 0.22/0.54          | ~ (l1_struct_0 @ X30)
% 0.22/0.54          | (v2_struct_0 @ X30))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      ((~ (v1_xboole_0 @ sk_B_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A)
% 0.22/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.54  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('17', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('19', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.54      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf(d1_xboole_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.54  thf(t140_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.54       ( ( k2_xboole_0 @
% 0.22/0.54           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.22/0.54         ( B ) ) ))).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X21 : $i, X22 : $i]:
% 0.22/0.54         (((k2_xboole_0 @ (k4_xboole_0 @ X21 @ (k1_tarski @ X22)) @ 
% 0.22/0.54            (k1_tarski @ X22)) = (X21))
% 0.22/0.54          | ~ (r2_hidden @ X22 @ X21))),
% 0.22/0.54      inference('cnf', [status(esa)], [t140_zfmisc_1])).
% 0.22/0.54  thf(commutativity_k2_tarski, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X11 : $i, X12 : $i]:
% 0.22/0.54         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.22/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.54  thf(l51_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i]:
% 0.22/0.54         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.22/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i]:
% 0.22/0.54         ((k3_tarski @ (k2_tarski @ X19 @ X20)) = (k2_xboole_0 @ X19 @ X20))),
% 0.22/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.54  thf(t39_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i]:
% 0.22/0.54         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.22/0.54           = (k2_xboole_0 @ X9 @ X10))),
% 0.22/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X21 : $i, X22 : $i]:
% 0.22/0.54         (((k2_xboole_0 @ (k1_tarski @ X22) @ X21) = (X21))
% 0.22/0.54          | ~ (r2_hidden @ X22 @ X21))),
% 0.22/0.54      inference('demod', [status(thm)], ['21', '26', '27'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ X0)
% 0.22/0.54          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['20', '28'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v1_xboole_0 @ X0)
% 0.22/0.54          | ((k2_xboole_0 @ X0 @ (k1_tarski @ (sk_B @ X0))) = (X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.54  thf(t49_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i]:
% 0.22/0.54         ((k2_xboole_0 @ (k1_tarski @ X23) @ X24) != (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.54  thf('34', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i]:
% 0.22/0.54         ((k2_xboole_0 @ (k1_tarski @ X23) @ X24) != (sk_B_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['32', '35'])).
% 0.22/0.54  thf('37', plain, (![X0 : $i]: (((X0) != (sk_B_1)) | (v1_xboole_0 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['31', '36'])).
% 0.22/0.54  thf('38', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.22/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.54  thf('39', plain, ($false), inference('demod', [status(thm)], ['19', '38'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
