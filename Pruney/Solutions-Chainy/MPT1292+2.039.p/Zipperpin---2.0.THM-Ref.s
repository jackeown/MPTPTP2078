%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5wTaHmghvG

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  92 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  290 ( 662 expanded)
%              Number of equality atoms :   20 (  44 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_setfam_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('3',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t60_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_setfam_1 @ X12 @ X11 )
      | ( ( k5_setfam_1 @ X11 @ X12 )
        = X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t60_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k5_setfam_1 @ X0 @ sk_B_1 )
        = X0 )
      | ~ ( m1_setfam_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k5_setfam_1 @ X4 @ X3 )
        = ( k3_tarski @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ sk_B_1 )
      = ( k3_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['10','11'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('14',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( X13 = sk_B_1 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_setfam_1 @ X0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ sk_B_1 )
      = ( k3_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B_1 )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['9','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = X0 )
      | ~ ( m1_setfam_1 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','25'])).

thf('27',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['10','11'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5wTaHmghvG
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 26 iterations in 0.016s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(t5_tops_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @
% 0.21/0.47             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.47                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @
% 0.21/0.47                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.47                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.21/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((m1_setfam_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t4_subset_1, axiom,
% 0.21/0.47    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.47  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(t60_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (m1_setfam_1 @ X12 @ X11)
% 0.21/0.47          | ((k5_setfam_1 @ X11 @ X12) = (X11))
% 0.21/0.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_setfam_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k5_setfam_1 @ X0 @ sk_B_1) = (X0)) | ~ (m1_setfam_1 @ sk_B_1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain, (![X0 : $i]: (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(redefinition_k5_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         (((k5_setfam_1 @ X4 @ X3) = (k3_tarski @ X3))
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]: ((k5_setfam_1 @ X0 @ sk_B_1) = (k3_tarski @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('11', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf(t6_mcart_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.47                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.47                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.21/0.47                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.21/0.47                       ( r2_hidden @ G @ B ) ) =>
% 0.21/0.47                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X13 : $i]:
% 0.21/0.47         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.21/0.47  thf('14', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X13 : $i]: (((X13) = (sk_B_1)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain, (![X0 : $i]: (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(dt_k5_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k5_setfam_1 @ X1 @ X2) @ (k1_zfmisc_1 @ X1))
% 0.21/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k5_setfam_1 @ X0 @ sk_B_1) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i]: ((k5_setfam_1 @ X0 @ sk_B_1) = (k3_tarski @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]: (m1_subset_1 @ (k3_tarski @ sk_B_1) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf(t5_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.47          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X8 @ X9)
% 0.21/0.47          | ~ (v1_xboole_0 @ X10)
% 0.21/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k3_tarski @ sk_B_1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i]: (((k3_tarski @ sk_B_1) = (sk_B_1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '22'])).
% 0.21/0.47  thf('24', plain, (((k3_tarski @ sk_B_1) = (sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '23'])).
% 0.21/0.47  thf('25', plain, (![X0 : $i]: ((k5_setfam_1 @ X0 @ sk_B_1) = (sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i]: (((sk_B_1) = (X0)) | ~ (m1_setfam_1 @ sk_B_1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['6', '25'])).
% 0.21/0.47  thf('27', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '26'])).
% 0.21/0.47  thf(fc2_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X19 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.21/0.47          | ~ (l1_struct_0 @ X19)
% 0.21/0.47          | (v2_struct_0 @ X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((~ (v1_xboole_0 @ sk_B_1)
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('32', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.47  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
