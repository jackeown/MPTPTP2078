%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MeJ7XNsLkb

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:59 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  264 ( 298 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( r1_tarski @ X13 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k9_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t144_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_relat_1])).

thf('13',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MeJ7XNsLkb
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 123 iterations in 0.183s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(d3_tarski, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (![X1 : $i, X3 : $i]:
% 0.45/0.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf(t143_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ C ) =>
% 0.45/0.67       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.45/0.67         ( ?[D:$i]:
% 0.45/0.67           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.67             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.45/0.67             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.45/0.67          | (r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X10 @ X11) @ X11) @ X12)
% 0.45/0.67          | ~ (v1_relat_1 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.67          | ~ (v1_relat_1 @ X1)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (k4_tarski @ 
% 0.45/0.67              (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.45/0.67              (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.45/0.67             X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.67  thf(t21_relat_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ A ) =>
% 0.45/0.67       ( r1_tarski @
% 0.45/0.67         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X13 : $i]:
% 0.45/0.67         ((r1_tarski @ X13 @ 
% 0.45/0.67           (k2_zfmisc_1 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 0.45/0.67          | ~ (v1_relat_1 @ X13))),
% 0.45/0.67      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.67          | (r2_hidden @ X0 @ X2)
% 0.45/0.67          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r2_hidden @ X1 @ 
% 0.45/0.67             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.45/0.67          | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.45/0.67          | (r2_hidden @ 
% 0.45/0.67             (k4_tarski @ 
% 0.45/0.67              (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ 
% 0.45/0.67              (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ 
% 0.45/0.67             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.45/0.67          | ~ (v1_relat_1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['2', '5'])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r2_hidden @ 
% 0.45/0.67           (k4_tarski @ 
% 0.45/0.67            (sk_D @ X0 @ X1 @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ 
% 0.45/0.67            (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1))) @ 
% 0.45/0.67           (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.45/0.67          | ~ (v1_relat_1 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['6'])).
% 0.45/0.67  thf(l54_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.45/0.67       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         ((r2_hidden @ X6 @ X7)
% 0.45/0.67          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 0.45/0.67      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.45/0.67          | (r2_hidden @ (sk_C @ X2 @ (k9_relat_1 @ X0 @ X1)) @ 
% 0.45/0.67             (k2_relat_1 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X1 : $i, X3 : $i]:
% 0.45/0.67         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.67  thf(t144_relat_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ B ) =>
% 0.45/0.67       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i]:
% 0.45/0.67        ( ( v1_relat_1 @ B ) =>
% 0.45/0.67          ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t144_relat_1])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('14', plain, (~ (v1_relat_1 @ sk_B)),
% 0.45/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('16', plain, ($false), inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
