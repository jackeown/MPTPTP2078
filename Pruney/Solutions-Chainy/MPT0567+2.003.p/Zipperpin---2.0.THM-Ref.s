%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M3cjPdnuId

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  205 ( 238 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X2: $i] :
      ( ( X2 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k10_relat_1 @ X35 @ X33 ) )
      | ( r2_hidden @ ( sk_D @ X35 @ X33 @ X34 ) @ X33 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X7 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X7: $i] :
      ( ( k6_subset_1 @ o_0_0_xboole_0 @ X7 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X26 )
      | ~ ( r2_hidden @ X24 @ ( k4_xboole_0 @ X25 @ ( k1_tarski @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ~ ( r2_hidden @ X26 @ ( k4_xboole_0 @ X25 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ~ ( r2_hidden @ X26 @ ( k6_subset_1 @ X25 @ ( k1_tarski @ X26 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(t171_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k10_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t171_relat_1])).

thf('17',plain,(
    ( k10_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('19',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('20',plain,(
    ( k10_relat_1 @ sk_A @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M3cjPdnuId
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 82 iterations in 0.046s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(t7_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.50  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.50  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X2 : $i]: (((X2) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf(t166_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.50         ( ?[D:$i]:
% 0.20/0.50           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.50             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.50             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X34 @ (k10_relat_1 @ X35 @ X33))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X35 @ X33 @ X34) @ X33)
% 0.20/0.50          | ~ (v1_relat_1 @ X35))),
% 0.20/0.50      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k10_relat_1 @ X1 @ X0) = (o_0_0_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.51             X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t4_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.51  thf('6', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.51  thf('7', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X7 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X7) = (o_0_0_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.51  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i]:
% 0.20/0.51         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X7 : $i]: ((k6_subset_1 @ o_0_0_xboole_0 @ X7) = (o_0_0_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf(t64_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.51       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.51         (((X24) != (X26))
% 0.20/0.51          | ~ (r2_hidden @ X24 @ (k4_xboole_0 @ X25 @ (k1_tarski @ X26))))),
% 0.20/0.51      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         ~ (r2_hidden @ X26 @ (k4_xboole_0 @ X25 @ (k1_tarski @ X26)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i]:
% 0.20/0.51         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         ~ (r2_hidden @ X26 @ (k6_subset_1 @ X25 @ (k1_tarski @ X26)))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ((k10_relat_1 @ X0 @ o_0_0_xboole_0) = (o_0_0_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.51  thf(t171_relat_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( v1_relat_1 @ A ) =>
% 0.20/0.51          ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t171_relat_1])).
% 0.20/0.51  thf('17', plain, (((k10_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.51  thf('19', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((k10_relat_1 @ sk_A @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '20'])).
% 0.20/0.51  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
