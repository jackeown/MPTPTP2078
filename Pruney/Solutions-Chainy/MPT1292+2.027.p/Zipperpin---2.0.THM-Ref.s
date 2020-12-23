%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.be1LTur9n6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  83 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  223 ( 584 expanded)
%              Number of equality atoms :   18 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_setfam_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t60_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_setfam_1 @ X11 @ X10 )
      | ( ( k5_setfam_1 @ X10 @ X11 )
        = X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[t60_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k5_setfam_1 @ X0 @ sk_B )
        = X0 )
      | ~ ( m1_setfam_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k5_setfam_1 @ X6 @ X5 )
        = ( k3_tarski @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ sk_B )
      = ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_tarski @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_setfam_1 @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( k3_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k5_setfam_1 @ X0 @ sk_B )
        = X0 )
      | ~ ( m1_setfam_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('18',plain,
    ( ( k5_setfam_1 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ X0 @ sk_B )
      = ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('20',plain,
    ( ( k3_tarski @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_B
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['11','20'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    sk_B = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.be1LTur9n6
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 26 iterations in 0.014s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.44  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.44  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.44  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.20/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.44  thf(t5_tops_2, conjecture,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @
% 0.20/0.44             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.44           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.44                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i]:
% 0.20/0.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.44          ( ![B:$i]:
% 0.20/0.44            ( ( m1_subset_1 @
% 0.20/0.44                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.44              ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.44                   ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t5_tops_2])).
% 0.20/0.44  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('1', plain, ((m1_setfam_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t4_subset_1, axiom,
% 0.20/0.44    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.20/0.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.44  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('4', plain, (![X1 : $i]: (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ X1))),
% 0.20/0.44      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.44  thf(t60_setfam_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.44       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X10 : $i, X11 : $i]:
% 0.20/0.44         (~ (m1_setfam_1 @ X11 @ X10)
% 0.20/0.44          | ((k5_setfam_1 @ X10 @ X11) = (X10))
% 0.20/0.44          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.20/0.44      inference('cnf', [status(esa)], [t60_setfam_1])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (((k5_setfam_1 @ X0 @ sk_B) = (X0)) | ~ (m1_setfam_1 @ sk_B @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.44  thf('8', plain, (![X1 : $i]: (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ X1))),
% 0.20/0.44      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.44  thf(redefinition_k5_setfam_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.44       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X5 : $i, X6 : $i]:
% 0.20/0.44         (((k5_setfam_1 @ X6 @ X5) = (k3_tarski @ X5))
% 0.20/0.44          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.20/0.44      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      (![X0 : $i]: ((k5_setfam_1 @ X0 @ sk_B) = (k3_tarski @ sk_B))),
% 0.20/0.44      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.44  thf('11', plain, (((k3_tarski @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.44  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.44  thf('12', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.44  thf('13', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('14', plain, (![X0 : $i]: (r1_tarski @ sk_B @ X0)),
% 0.20/0.44      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.44  thf(d12_setfam_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X2 : $i, X4 : $i]:
% 0.20/0.44         ((m1_setfam_1 @ X4 @ X2) | ~ (r1_tarski @ X2 @ (k3_tarski @ X4)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.20/0.44  thf('16', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ sk_B)),
% 0.20/0.44      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.44  thf('17', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (((k5_setfam_1 @ X0 @ sk_B) = (X0)) | ~ (m1_setfam_1 @ sk_B @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.44  thf('18', plain, (((k5_setfam_1 @ sk_B @ sk_B) = (sk_B))),
% 0.20/0.44      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.44  thf('19', plain,
% 0.20/0.44      (![X0 : $i]: ((k5_setfam_1 @ X0 @ sk_B) = (k3_tarski @ sk_B))),
% 0.20/0.44      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.44  thf('20', plain, (((k3_tarski @ sk_B) = (sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.44  thf('21', plain, (((sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['11', '20'])).
% 0.20/0.44  thf(fc2_struct_0, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.44       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.44  thf('22', plain,
% 0.20/0.44      (![X12 : $i]:
% 0.20/0.44         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.20/0.44          | ~ (l1_struct_0 @ X12)
% 0.20/0.44          | (v2_struct_0 @ X12))),
% 0.20/0.44      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.44  thf('23', plain,
% 0.20/0.44      ((~ (v1_xboole_0 @ sk_B) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.44  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.44  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.44  thf('25', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('26', plain, ((v1_xboole_0 @ sk_B)),
% 0.20/0.44      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.44  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('28', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('demod', [status(thm)], ['23', '26', '27'])).
% 0.20/0.44  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
