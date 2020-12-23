%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.urEbbkrWEv

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:01 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   50 (  53 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 ( 296 expanded)
%              Number of equality atoms :   27 (  30 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( sk_B @ X38 ) @ X38 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k9_relat_1 @ X42 @ X40 ) )
      | ( r2_hidden @ ( sk_D @ X42 @ X40 @ X41 ) @ X40 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t68_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X32: $i,X34: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ X34 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t68_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ ( sk_D @ X0 @ k1_xboole_0 @ ( sk_B @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30 != X29 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X29 ) )
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X29 ) )
     != ( k1_tarski @ X29 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X29: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X29 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['8','16'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t149_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k9_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t149_relat_1])).

thf('20',plain,(
    ( k9_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.urEbbkrWEv
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.90  % Solved by: fo/fo7.sh
% 0.67/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.90  % done 395 iterations in 0.444s
% 0.67/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.90  % SZS output start Refutation
% 0.67/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.90  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.67/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.90  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.67/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.67/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.90  thf(existence_m1_subset_1, axiom,
% 0.67/0.90    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.67/0.90  thf('0', plain, (![X38 : $i]: (m1_subset_1 @ (sk_B @ X38) @ X38)),
% 0.67/0.90      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.67/0.90  thf(d2_subset_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( v1_xboole_0 @ A ) =>
% 0.67/0.90         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.67/0.90       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.67/0.90         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.90  thf('1', plain,
% 0.67/0.90      (![X35 : $i, X36 : $i]:
% 0.67/0.90         (~ (m1_subset_1 @ X35 @ X36)
% 0.67/0.90          | (r2_hidden @ X35 @ X36)
% 0.67/0.90          | (v1_xboole_0 @ X36))),
% 0.67/0.90      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.67/0.90  thf('2', plain,
% 0.67/0.90      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['0', '1'])).
% 0.67/0.90  thf(t143_relat_1, axiom,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( v1_relat_1 @ C ) =>
% 0.67/0.90       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.67/0.90         ( ?[D:$i]:
% 0.67/0.90           ( ( r2_hidden @ D @ B ) & 
% 0.67/0.90             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.67/0.90             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.67/0.90  thf('3', plain,
% 0.67/0.90      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.67/0.90         (~ (r2_hidden @ X41 @ (k9_relat_1 @ X42 @ X40))
% 0.67/0.90          | (r2_hidden @ (sk_D @ X42 @ X40 @ X41) @ X40)
% 0.67/0.90          | ~ (v1_relat_1 @ X42))),
% 0.67/0.90      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.67/0.90  thf('4', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.67/0.90          | ~ (v1_relat_1 @ X1)
% 0.67/0.90          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.67/0.90             X0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.90  thf(t68_zfmisc_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.67/0.90       ( r2_hidden @ A @ B ) ))).
% 0.67/0.90  thf('5', plain,
% 0.67/0.90      (![X32 : $i, X34 : $i]:
% 0.67/0.90         (((k4_xboole_0 @ (k1_tarski @ X32) @ X34) = (k1_xboole_0))
% 0.67/0.90          | ~ (r2_hidden @ X32 @ X34))),
% 0.67/0.90      inference('cnf', [status(esa)], [t68_zfmisc_1])).
% 0.67/0.90  thf('6', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         (~ (v1_relat_1 @ X1)
% 0.67/0.90          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.67/0.90          | ((k4_xboole_0 @ 
% 0.67/0.90              (k1_tarski @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0)))) @ 
% 0.67/0.90              X0) = (k1_xboole_0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['4', '5'])).
% 0.67/0.90  thf(t3_boole, axiom,
% 0.67/0.90    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.90  thf('7', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.90  thf('8', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k1_xboole_0)
% 0.67/0.90            = (k1_tarski @ 
% 0.67/0.90               (sk_D @ X0 @ k1_xboole_0 @ 
% 0.67/0.90                (sk_B @ (k9_relat_1 @ X0 @ k1_xboole_0)))))
% 0.67/0.90          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.90          | ~ (v1_relat_1 @ X0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['6', '7'])).
% 0.67/0.90  thf(t20_zfmisc_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.67/0.90         ( k1_tarski @ A ) ) <=>
% 0.67/0.90       ( ( A ) != ( B ) ) ))).
% 0.67/0.90  thf('9', plain,
% 0.67/0.90      (![X29 : $i, X30 : $i]:
% 0.67/0.90         (((X30) != (X29))
% 0.67/0.90          | ((k4_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X29))
% 0.67/0.90              != (k1_tarski @ X30)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.67/0.90  thf('10', plain,
% 0.67/0.90      (![X29 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X29))
% 0.67/0.90           != (k1_tarski @ X29))),
% 0.67/0.90      inference('simplify', [status(thm)], ['9'])).
% 0.67/0.90  thf('11', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.67/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.90  thf(t48_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.67/0.90  thf('12', plain,
% 0.67/0.90      (![X2 : $i, X3 : $i]:
% 0.67/0.90         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.67/0.90           = (k3_xboole_0 @ X2 @ X3))),
% 0.67/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.90  thf('13', plain,
% 0.67/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['11', '12'])).
% 0.67/0.90  thf(t2_boole, axiom,
% 0.67/0.90    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.67/0.90  thf('14', plain,
% 0.67/0.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.90      inference('cnf', [status(esa)], [t2_boole])).
% 0.67/0.90  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.90      inference('demod', [status(thm)], ['13', '14'])).
% 0.67/0.90  thf('16', plain, (![X29 : $i]: ((k1_xboole_0) != (k1_tarski @ X29))),
% 0.67/0.90      inference('demod', [status(thm)], ['10', '15'])).
% 0.67/0.90  thf('17', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.67/0.90      inference('clc', [status(thm)], ['8', '16'])).
% 0.67/0.90  thf(t6_boole, axiom,
% 0.67/0.90    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.90  thf('18', plain,
% 0.67/0.90      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.67/0.90      inference('cnf', [status(esa)], [t6_boole])).
% 0.67/0.90  thf('19', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (v1_relat_1 @ X0)
% 0.67/0.90          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['17', '18'])).
% 0.67/0.90  thf(t149_relat_1, conjecture,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( v1_relat_1 @ A ) =>
% 0.67/0.90       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.90    (~( ![A:$i]:
% 0.67/0.90        ( ( v1_relat_1 @ A ) =>
% 0.67/0.90          ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.67/0.90    inference('cnf.neg', [status(esa)], [t149_relat_1])).
% 0.67/0.90  thf('20', plain, (((k9_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('21', plain,
% 0.67/0.90      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.67/0.90      inference('sup-', [status(thm)], ['19', '20'])).
% 0.67/0.90  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('23', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.67/0.90      inference('demod', [status(thm)], ['21', '22'])).
% 0.67/0.90  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.67/0.90  
% 0.67/0.90  % SZS output end Refutation
% 0.67/0.90  
% 0.67/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
