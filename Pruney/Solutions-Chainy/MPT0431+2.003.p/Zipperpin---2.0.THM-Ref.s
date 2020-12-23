%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oVTpC7s5v9

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:37 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   46 (  64 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  338 ( 760 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t63_setfam_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v3_setfam_1 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v3_setfam_1 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
             => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v3_setfam_1 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
           => ! [C: $i] :
                ( ( ( v3_setfam_1 @ C @ A )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
               => ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v3_setfam_1 @ B @ A )
      <=> ~ ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_setfam_1 @ X13 @ X12 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( v3_setfam_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_setfam_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v3_setfam_1 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('11',plain,
    ( ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['13','18'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_setfam_1 @ X13 @ X12 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['22','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['4','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oVTpC7s5v9
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:55:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 158 iterations in 0.141s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.41/0.59  thf(t63_setfam_1, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.41/0.59             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.41/0.59                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.41/0.59               ( v3_setfam_1 @
% 0.41/0.59                 ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.59          ( ![B:$i]:
% 0.41/0.59            ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.41/0.59                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.41/0.59              ( ![C:$i]:
% 0.41/0.59                ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.41/0.59                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.41/0.59                  ( v3_setfam_1 @
% 0.41/0.59                    ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t63_setfam_1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(d13_setfam_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (v3_setfam_1 @ X13 @ X12)
% 0.41/0.59          | ~ (r2_hidden @ X12 @ X13)
% 0.41/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.41/0.59      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      ((~ (r2_hidden @ sk_A @ sk_C) | ~ (v3_setfam_1 @ sk_C @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf('3', plain, ((v3_setfam_1 @ sk_C @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('4', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(dt_k4_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.41/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.41/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 0.41/0.59          | (m1_subset_1 @ (k4_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0) @ 
% 0.41/0.59           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.41/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['5', '8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         ((r2_hidden @ X12 @ X13)
% 0.41/0.59          | (v3_setfam_1 @ X13 @ X12)
% 0.41/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.41/0.59      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (((v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.41/0.59         sk_A)
% 0.41/0.59        | (r2_hidden @ sk_A @ 
% 0.41/0.59           (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (~ (v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.41/0.59          sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      ((r2_hidden @ sk_A @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C))),
% 0.41/0.59      inference('clc', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(redefinition_k4_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.41/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.41/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 0.41/0.59          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0)
% 0.41/0.59            = (k2_xboole_0 @ sk_B @ X0))
% 0.41/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C)
% 0.41/0.59         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['14', '17'])).
% 0.41/0.59  thf('19', plain, ((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['13', '18'])).
% 0.41/0.59  thf(d3_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.41/0.59       ( ![D:$i]:
% 0.41/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.59           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X4 @ X2)
% 0.41/0.59          | (r2_hidden @ X4 @ X3)
% 0.41/0.59          | (r2_hidden @ X4 @ X1)
% 0.41/0.59          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.41/0.59         ((r2_hidden @ X4 @ X1)
% 0.41/0.59          | (r2_hidden @ X4 @ X3)
% 0.41/0.59          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['20'])).
% 0.41/0.59  thf('22', plain, (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['19', '21'])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (v3_setfam_1 @ X13 @ X12)
% 0.41/0.59          | ~ (r2_hidden @ X12 @ X13)
% 0.41/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.41/0.59      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (v3_setfam_1 @ sk_B @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.59  thf('26', plain, ((v3_setfam_1 @ sk_B @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('27', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.41/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.41/0.59  thf('28', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.41/0.59      inference('clc', [status(thm)], ['22', '27'])).
% 0.41/0.59  thf('29', plain, ($false), inference('demod', [status(thm)], ['4', '28'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
