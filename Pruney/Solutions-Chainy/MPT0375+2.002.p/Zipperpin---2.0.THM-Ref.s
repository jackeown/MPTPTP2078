%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.81Yu3uV1ym

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:24 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 115 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  371 (1073 expanded)
%              Number of equality atoms :   23 (  77 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t57_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ A )
             => ( ( A != k1_xboole_0 )
               => ( m1_subset_1 @ ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ A )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( A != k1_xboole_0 )
                 => ( m1_subset_1 @ ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_subset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_enumset1 @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ( ( A != k1_xboole_0 )
           => ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ X38 )
      | ( m1_subset_1 @ ( k2_tarski @ X39 @ X37 ) @ ( k1_zfmisc_1 @ X38 ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t56_subset_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ X38 )
      | ( m1_subset_1 @ ( k2_tarski @ X39 @ X37 ) @ ( k1_zfmisc_1 @ X38 ) )
      | ( X38 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ X38 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_A = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( k2_tarski @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k2_tarski @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ X38 )
      | ( m1_subset_1 @ ( k2_tarski @ X39 @ X37 ) @ ( k1_zfmisc_1 @ X38 ) )
      | ( X38 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ X38 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_A = o_0_0_xboole_0 )
      | ( m1_subset_1 @ ( k2_tarski @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k2_tarski @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_tarski @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X32 @ X31 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_subset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('30',plain,
    ( ( k4_subset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k1_enumset1 @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_enumset1 @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.81Yu3uV1ym
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:59:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 162 iterations in 0.136s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.60  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.37/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.60  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.37/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.60  thf(t57_subset_1, conjecture,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ B @ A ) =>
% 0.37/0.60       ( ![C:$i]:
% 0.37/0.60         ( ( m1_subset_1 @ C @ A ) =>
% 0.37/0.60           ( ![D:$i]:
% 0.37/0.60             ( ( m1_subset_1 @ D @ A ) =>
% 0.37/0.60               ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.37/0.60                 ( m1_subset_1 @
% 0.37/0.60                   ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i]:
% 0.37/0.60        ( ( m1_subset_1 @ B @ A ) =>
% 0.37/0.60          ( ![C:$i]:
% 0.37/0.60            ( ( m1_subset_1 @ C @ A ) =>
% 0.37/0.60              ( ![D:$i]:
% 0.37/0.60                ( ( m1_subset_1 @ D @ A ) =>
% 0.37/0.60                  ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.37/0.60                    ( m1_subset_1 @
% 0.37/0.60                      ( k1_enumset1 @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t57_subset_1])).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      (~ (m1_subset_1 @ (k1_enumset1 @ sk_B @ sk_C @ sk_D) @ 
% 0.37/0.60          (k1_zfmisc_1 @ sk_A))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('1', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('2', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(t56_subset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ B @ A ) =>
% 0.37/0.60       ( ![C:$i]:
% 0.37/0.60         ( ( m1_subset_1 @ C @ A ) =>
% 0.37/0.60           ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.37/0.60             ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X37 @ X38)
% 0.37/0.60          | (m1_subset_1 @ (k2_tarski @ X39 @ X37) @ (k1_zfmisc_1 @ X38))
% 0.37/0.60          | ((X38) = (k1_xboole_0))
% 0.37/0.60          | ~ (m1_subset_1 @ X39 @ X38))),
% 0.37/0.60      inference('cnf', [status(esa)], [t56_subset_1])).
% 0.37/0.60  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.37/0.60  thf('4', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X37 @ X38)
% 0.37/0.60          | (m1_subset_1 @ (k2_tarski @ X39 @ X37) @ (k1_zfmisc_1 @ X38))
% 0.37/0.60          | ((X38) = (o_0_0_xboole_0))
% 0.37/0.60          | ~ (m1_subset_1 @ X39 @ X38))),
% 0.37/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.37/0.60          | ((sk_A) = (o_0_0_xboole_0))
% 0.37/0.60          | (m1_subset_1 @ (k2_tarski @ X0 @ sk_D) @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['2', '5'])).
% 0.37/0.60  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('8', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.37/0.60  thf('9', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.37/0.60          | (m1_subset_1 @ (k2_tarski @ X0 @ sk_D) @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.60      inference('simplify_reflect-', [status(thm)], ['6', '9'])).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      ((m1_subset_1 @ (k2_tarski @ sk_C @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['1', '10'])).
% 0.37/0.60  thf('12', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('13', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('14', plain,
% 0.37/0.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X37 @ X38)
% 0.37/0.60          | (m1_subset_1 @ (k2_tarski @ X39 @ X37) @ (k1_zfmisc_1 @ X38))
% 0.37/0.60          | ((X38) = (o_0_0_xboole_0))
% 0.37/0.60          | ~ (m1_subset_1 @ X39 @ X38))),
% 0.37/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.37/0.60          | ((sk_A) = (o_0_0_xboole_0))
% 0.37/0.60          | (m1_subset_1 @ (k2_tarski @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.60  thf('16', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.37/0.60          | (m1_subset_1 @ (k2_tarski @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.60      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      ((m1_subset_1 @ (k2_tarski @ sk_B @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['12', '17'])).
% 0.37/0.60  thf(t69_enumset1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.60  thf('19', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.37/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.60  thf('20', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.60  thf(dt_k4_subset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.37/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.60       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.37/0.60          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 0.37/0.60          | (m1_subset_1 @ (k4_subset_1 @ X32 @ X31 @ X33) @ 
% 0.37/0.60             (k1_zfmisc_1 @ X32)))),
% 0.37/0.60      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0) @ 
% 0.37/0.60           (k1_zfmisc_1 @ sk_A))
% 0.37/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      ((m1_subset_1 @ 
% 0.37/0.60        (k4_subset_1 @ sk_A @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D)) @ 
% 0.37/0.60        (k1_zfmisc_1 @ sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['11', '22'])).
% 0.37/0.60  thf('24', plain,
% 0.37/0.60      ((m1_subset_1 @ (k2_tarski @ sk_C @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['1', '10'])).
% 0.37/0.60  thf('25', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.60  thf(redefinition_k4_subset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.37/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.60       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.37/0.60          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 0.37/0.60          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (((k4_subset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0)
% 0.37/0.60            = (k2_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 0.37/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.60  thf('28', plain,
% 0.37/0.60      (((k4_subset_1 @ sk_A @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.37/0.60         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['24', '27'])).
% 0.37/0.60  thf(t42_enumset1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.37/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.60         ((k1_enumset1 @ X0 @ X1 @ X2)
% 0.37/0.60           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X2)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (((k4_subset_1 @ sk_A @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.37/0.60         = (k1_enumset1 @ sk_B @ sk_C @ sk_D))),
% 0.37/0.60      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      ((m1_subset_1 @ (k1_enumset1 @ sk_B @ sk_C @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.60      inference('demod', [status(thm)], ['23', '30'])).
% 0.37/0.60  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
