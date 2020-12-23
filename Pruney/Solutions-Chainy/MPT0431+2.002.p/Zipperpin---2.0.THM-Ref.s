%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kzHGP3Hl5P

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   57 (  75 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  395 ( 817 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v3_setfam_1 @ B @ A )
      <=> ~ ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_setfam_1 @ X26 @ X25 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( v3_setfam_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_setfam_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( v3_setfam_1 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('11',plain,
    ( ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A )
    | ( r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v3_setfam_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k4_subset_1 @ X23 @ X22 @ X24 )
        = ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','18'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_setfam_1 @ X26 @ X25 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['23','28'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['4','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kzHGP3Hl5P
% 0.14/0.37  % Computer   : n024.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:59:51 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.56  % Solved by: fo/fo7.sh
% 0.23/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.56  % done 85 iterations in 0.069s
% 0.23/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.56  % SZS output start Refutation
% 0.23/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.56  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 0.23/0.56  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.23/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.56  thf(t63_setfam_1, conjecture,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.23/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.23/0.56           ( ![C:$i]:
% 0.23/0.56             ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.23/0.56                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.23/0.56               ( v3_setfam_1 @
% 0.23/0.56                 ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ))).
% 0.23/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.56    (~( ![A:$i]:
% 0.23/0.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.56          ( ![B:$i]:
% 0.23/0.56            ( ( ( v3_setfam_1 @ B @ A ) & 
% 0.23/0.56                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.23/0.56              ( ![C:$i]:
% 0.23/0.56                ( ( ( v3_setfam_1 @ C @ A ) & 
% 0.23/0.56                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.23/0.56                  ( v3_setfam_1 @
% 0.23/0.56                    ( k4_subset_1 @ ( k1_zfmisc_1 @ A ) @ B @ C ) @ A ) ) ) ) ) ) )),
% 0.23/0.56    inference('cnf.neg', [status(esa)], [t63_setfam_1])).
% 0.23/0.56  thf('0', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(d13_setfam_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.56       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 0.23/0.56  thf('1', plain,
% 0.23/0.56      (![X25 : $i, X26 : $i]:
% 0.23/0.56         (~ (v3_setfam_1 @ X26 @ X25)
% 0.23/0.56          | ~ (r2_hidden @ X25 @ X26)
% 0.23/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 0.23/0.56      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.23/0.56  thf('2', plain,
% 0.23/0.56      ((~ (r2_hidden @ sk_A @ sk_C_1) | ~ (v3_setfam_1 @ sk_C_1 @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.56  thf('3', plain, ((v3_setfam_1 @ sk_C_1 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('4', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.23/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.56  thf('5', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('6', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(dt_k4_subset_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.23/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.56       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.56  thf('7', plain,
% 0.23/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.23/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.23/0.56          | (m1_subset_1 @ (k4_subset_1 @ X20 @ X19 @ X21) @ 
% 0.23/0.56             (k1_zfmisc_1 @ X20)))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.23/0.56  thf('8', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0) @ 
% 0.23/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.23/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.56  thf('9', plain,
% 0.23/0.56      ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C_1) @ 
% 0.23/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['5', '8'])).
% 0.23/0.56  thf('10', plain,
% 0.23/0.56      (![X25 : $i, X26 : $i]:
% 0.23/0.56         ((r2_hidden @ X25 @ X26)
% 0.23/0.56          | (v3_setfam_1 @ X26 @ X25)
% 0.23/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 0.23/0.56      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.23/0.56  thf('11', plain,
% 0.23/0.56      (((v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C_1) @ 
% 0.23/0.56         sk_A)
% 0.23/0.56        | (r2_hidden @ sk_A @ 
% 0.23/0.56           (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.56  thf('12', plain,
% 0.23/0.56      (~ (v3_setfam_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C_1) @ 
% 0.23/0.56          sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('13', plain,
% 0.23/0.56      ((r2_hidden @ sk_A @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.23/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.23/0.56  thf('14', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('15', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(redefinition_k4_subset_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.23/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.56       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.23/0.56  thf('16', plain,
% 0.23/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.23/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 0.23/0.56          | ((k4_subset_1 @ X23 @ X22 @ X24) = (k2_xboole_0 @ X22 @ X24)))),
% 0.23/0.56      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.23/0.56  thf('17', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0)
% 0.23/0.56            = (k2_xboole_0 @ sk_B @ X0))
% 0.23/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.56  thf('18', plain,
% 0.23/0.56      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ sk_C_1)
% 0.23/0.56         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['14', '17'])).
% 0.23/0.56  thf('19', plain, ((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.23/0.56      inference('demod', [status(thm)], ['13', '18'])).
% 0.23/0.56  thf(t98_xboole_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.23/0.56  thf('20', plain,
% 0.23/0.56      (![X10 : $i, X11 : $i]:
% 0.23/0.56         ((k2_xboole_0 @ X10 @ X11)
% 0.23/0.56           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.23/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.23/0.56  thf(t1_xboole_0, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i]:
% 0.23/0.56     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.23/0.56       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.23/0.56  thf('21', plain,
% 0.23/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.56         ((r2_hidden @ X4 @ X5)
% 0.23/0.56          | (r2_hidden @ X4 @ X6)
% 0.23/0.56          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.23/0.56      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.23/0.56  thf('22', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.23/0.56          | (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.23/0.56          | (r2_hidden @ X2 @ X1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.56  thf('23', plain,
% 0.23/0.56      (((r2_hidden @ sk_A @ sk_B)
% 0.23/0.56        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['19', '22'])).
% 0.23/0.56  thf('24', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('25', plain,
% 0.23/0.56      (![X25 : $i, X26 : $i]:
% 0.23/0.56         (~ (v3_setfam_1 @ X26 @ X25)
% 0.23/0.56          | ~ (r2_hidden @ X25 @ X26)
% 0.23/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 0.23/0.56      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.23/0.56  thf('26', plain,
% 0.23/0.56      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (v3_setfam_1 @ sk_B @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.56  thf('27', plain, ((v3_setfam_1 @ sk_B @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('28', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.23/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.23/0.56  thf('29', plain, ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 0.23/0.56      inference('clc', [status(thm)], ['23', '28'])).
% 0.23/0.56  thf(t36_xboole_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.23/0.56  thf('30', plain,
% 0.23/0.56      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.23/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.23/0.56  thf(d3_tarski, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.56  thf('31', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.56          | (r2_hidden @ X0 @ X2)
% 0.23/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.23/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.56  thf('32', plain,
% 0.23/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.56         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.56  thf('33', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.23/0.56      inference('sup-', [status(thm)], ['29', '32'])).
% 0.23/0.56  thf('34', plain, ($false), inference('demod', [status(thm)], ['4', '33'])).
% 0.23/0.56  
% 0.23/0.56  % SZS output end Refutation
% 0.23/0.56  
% 0.23/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
