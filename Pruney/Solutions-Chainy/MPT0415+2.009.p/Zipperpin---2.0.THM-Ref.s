%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VPaC6Sn7EG

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  66 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  319 ( 516 expanded)
%              Number of equality atoms :   23 (  51 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k7_setfam_1 @ X42 @ ( k7_setfam_1 @ X42 @ X41 ) )
        = X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('3',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['3','4'])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X38 ) ) )
      | ( X37
       != ( k7_setfam_1 @ X38 @ X39 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X38 @ X40 ) @ X39 )
      | ~ ( r2_hidden @ X40 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r2_hidden @ X40 @ ( k7_setfam_1 @ X38 @ X39 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X38 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X38 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['3','4'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X35: $i] :
      ( ( k1_subset_1 @ X35 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X36 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','13'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ( ( k4_xboole_0 @ X33 @ ( k1_tarski @ X32 ) )
       != X33 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['14','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('21',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( m1_subset_1 @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['19','22'])).

thf('24',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VPaC6Sn7EG
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:37:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 96 iterations in 0.043s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.52  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(t7_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.52  thf(t46_setfam_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(involutiveness_k7_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X41 : $i, X42 : $i]:
% 0.20/0.52         (((k7_setfam_1 @ X42 @ (k7_setfam_1 @ X42 @ X41)) = (X41))
% 0.20/0.52          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X42))))),
% 0.20/0.52      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain, (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(d8_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.52             ( ![D:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52                 ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X38)))
% 0.20/0.52          | ((X37) != (k7_setfam_1 @ X38 @ X39))
% 0.20/0.52          | (r2_hidden @ (k3_subset_1 @ X38 @ X40) @ X39)
% 0.20/0.52          | ~ (r2_hidden @ X40 @ X37)
% 0.20/0.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X38))
% 0.20/0.52          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X38))))),
% 0.20/0.52      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X38)))
% 0.20/0.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X38))
% 0.20/0.52          | ~ (r2_hidden @ X40 @ (k7_setfam_1 @ X38 @ X39))
% 0.20/0.52          | (r2_hidden @ (k3_subset_1 @ X38 @ X40) @ X39)
% 0.20/0.52          | ~ (m1_subset_1 @ (k7_setfam_1 @ X38 @ X39) @ 
% 0.20/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X38))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.52          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('11', plain, (![X35 : $i]: ((k1_subset_1 @ X35) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.52  thf(dt_k1_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X36 : $i]: (m1_subset_1 @ (k1_subset_1 @ X36) @ (k1_zfmisc_1 @ X36))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9', '10', '13'])).
% 0.20/0.52  thf(t4_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X3 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.52  thf(t65_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.52       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X32 : $i, X33 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X32 @ X33)
% 0.20/0.52          | ((k4_xboole_0 @ X33 @ (k1_tarski @ X32)) != (X33)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.52      inference('clc', [status(thm)], ['14', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t4_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X45 @ X46)
% 0.20/0.52          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.20/0.52          | (m1_subset_1 @ X45 @ X47))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.20/0.52      inference('clc', [status(thm)], ['19', '22'])).
% 0.20/0.52  thf('24', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '23'])).
% 0.20/0.52  thf('25', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
