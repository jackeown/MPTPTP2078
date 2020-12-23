%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hf0cFSTpF2

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:09 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  202 ( 316 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t215_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t215_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ~ ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      = ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_A ) ) )
        = sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_A ) ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hf0cFSTpF2
% 0.12/0.31  % Computer   : n003.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 15:02:12 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.32  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 23 iterations in 0.021s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.45  thf(t215_relat_1, conjecture,
% 0.18/0.45    (![A:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ A ) =>
% 0.18/0.45       ( ![B:$i]:
% 0.18/0.45         ( ( v1_relat_1 @ B ) =>
% 0.18/0.45           ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.18/0.45             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i]:
% 0.18/0.45        ( ( v1_relat_1 @ A ) =>
% 0.18/0.45          ( ![B:$i]:
% 0.18/0.45            ( ( v1_relat_1 @ B ) =>
% 0.18/0.45              ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.18/0.45                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t215_relat_1])).
% 0.18/0.45  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('1', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(t127_zfmisc_1, axiom,
% 0.18/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.45     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.18/0.45       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.18/0.45  thf('2', plain,
% 0.18/0.45      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.18/0.45         ((r1_xboole_0 @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X9))
% 0.18/0.45          | ~ (r1_xboole_0 @ X7 @ X9))),
% 0.18/0.45      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.18/0.45  thf('3', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ sk_A)) @ 
% 0.18/0.45          (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.18/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.45  thf(t83_xboole_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.18/0.45  thf('4', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         (((k4_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.18/0.45      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.18/0.45  thf('5', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         ((k4_xboole_0 @ (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ sk_A)) @ 
% 0.18/0.45           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.18/0.45           = (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ sk_A)))),
% 0.18/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.18/0.45  thf(t21_relat_1, axiom,
% 0.18/0.45    (![A:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ A ) =>
% 0.18/0.45       ( r1_tarski @
% 0.18/0.45         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.18/0.45  thf('6', plain,
% 0.18/0.45      (![X10 : $i]:
% 0.18/0.45         ((r1_tarski @ X10 @ 
% 0.18/0.45           (k2_zfmisc_1 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.18/0.45          | ~ (v1_relat_1 @ X10))),
% 0.18/0.45      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.18/0.46  thf(t85_xboole_1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X3 @ X4)
% 0.18/0.46          | (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X5 @ X4)))),
% 0.18/0.46      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.18/0.46  thf('8', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (~ (v1_relat_1 @ X0)
% 0.18/0.46          | (r1_xboole_0 @ X0 @ 
% 0.18/0.46             (k4_xboole_0 @ X1 @ 
% 0.18/0.46              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.46  thf('9', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (((k4_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.18/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.18/0.46  thf('10', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (~ (v1_relat_1 @ X0)
% 0.18/0.46          | ((k4_xboole_0 @ X0 @ 
% 0.18/0.46              (k4_xboole_0 @ X1 @ 
% 0.18/0.46               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.18/0.46              = (X0)))),
% 0.18/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.46  thf('11', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (((k4_xboole_0 @ sk_B @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_A)))
% 0.18/0.46            = (sk_B))
% 0.18/0.46          | ~ (v1_relat_1 @ sk_B))),
% 0.18/0.46      inference('sup+', [status(thm)], ['5', '10'])).
% 0.18/0.46  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('13', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         ((k4_xboole_0 @ sk_B @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_A)))
% 0.18/0.46           = (sk_B))),
% 0.18/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.18/0.46  thf('14', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (~ (v1_relat_1 @ X0)
% 0.18/0.46          | (r1_xboole_0 @ X0 @ 
% 0.18/0.46             (k4_xboole_0 @ X1 @ 
% 0.18/0.46              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.18/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.46  thf('15', plain, (((r1_xboole_0 @ sk_A @ sk_B) | ~ (v1_relat_1 @ sk_A))),
% 0.18/0.46      inference('sup+', [status(thm)], ['13', '14'])).
% 0.18/0.46  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('17', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.18/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.18/0.46  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
