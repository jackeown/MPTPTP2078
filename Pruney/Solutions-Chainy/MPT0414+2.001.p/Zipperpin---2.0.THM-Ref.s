%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6xw8t4rcxj

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  315 ( 562 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t44_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_setfam_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_C_1 )
      | ( r2_hidden @ X11 @ sk_B )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(simplify,[status(thm)],['10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_B )
      | ( r2_hidden @ X11 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_C_1 = sk_B ),
    inference('sup+',[status(thm)],['15','29'])).

thf('31',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6xw8t4rcxj
% 0.12/0.35  % Computer   : n021.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 11:31:34 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 33 iterations in 0.011s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.43  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.43  thf(d3_tarski, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.43       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.43  thf('0', plain,
% 0.20/0.43      (![X3 : $i, X5 : $i]:
% 0.20/0.43         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf(t44_setfam_1, conjecture,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.43       ( ![C:$i]:
% 0.20/0.43         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.43           ( ( ![D:$i]:
% 0.20/0.43               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.43                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.43             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i]:
% 0.20/0.43        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.43          ( ![C:$i]:
% 0.20/0.43            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.43              ( ( ![D:$i]:
% 0.20/0.43                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.43                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.43                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(t4_subset, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.43       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.43          | (m1_subset_1 @ X8 @ X10))),
% 0.20/0.43      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.43          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.43      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.43          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X11 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X11 @ sk_C_1)
% 0.20/0.43          | (r2_hidden @ X11 @ sk_B)
% 0.20/0.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.43          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.20/0.43          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))),
% 0.20/0.43      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.43  thf('7', plain,
% 0.20/0.43      (![X3 : $i, X5 : $i]:
% 0.20/0.43         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B) | (r1_tarski @ sk_C_1 @ X0))),
% 0.20/0.43      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      (![X3 : $i, X5 : $i]:
% 0.20/0.43         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf('10', plain,
% 0.20/0.43      (((r1_tarski @ sk_C_1 @ sk_B) | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.43  thf('11', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.20/0.43      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.43  thf(t28_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.43  thf('12', plain,
% 0.20/0.43      (![X6 : $i, X7 : $i]:
% 0.20/0.43         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.43  thf('13', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 0.20/0.43      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.43  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.43    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.43  thf('14', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.43      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.43  thf('15', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_C_1))),
% 0.20/0.43      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.43  thf('16', plain,
% 0.20/0.43      (![X3 : $i, X5 : $i]:
% 0.20/0.43         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf('17', plain,
% 0.20/0.43      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('18', plain,
% 0.20/0.43      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.43          | (m1_subset_1 @ X8 @ X10))),
% 0.20/0.43      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.43  thf('19', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.43  thf('20', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ sk_B @ X0)
% 0.20/0.43          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.43  thf('21', plain,
% 0.20/0.43      (![X11 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X11 @ sk_B)
% 0.20/0.43          | (r2_hidden @ X11 @ sk_C_1)
% 0.20/0.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('22', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ sk_B @ X0)
% 0.20/0.43          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1)
% 0.20/0.43          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.43  thf('23', plain,
% 0.20/0.43      (![X3 : $i, X5 : $i]:
% 0.20/0.43         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf('24', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1) | (r1_tarski @ sk_B @ X0))),
% 0.20/0.43      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.43  thf('25', plain,
% 0.20/0.43      (![X3 : $i, X5 : $i]:
% 0.20/0.43         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf('26', plain,
% 0.20/0.43      (((r1_tarski @ sk_B @ sk_C_1) | (r1_tarski @ sk_B @ sk_C_1))),
% 0.20/0.43      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.43  thf('27', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.20/0.43      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.43  thf('28', plain,
% 0.20/0.43      (![X6 : $i, X7 : $i]:
% 0.20/0.43         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.43      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.43  thf('29', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.43  thf('30', plain, (((sk_C_1) = (sk_B))),
% 0.20/0.43      inference('sup+', [status(thm)], ['15', '29'])).
% 0.20/0.43  thf('31', plain, (((sk_B) != (sk_C_1))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('32', plain, ($false),
% 0.20/0.43      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
