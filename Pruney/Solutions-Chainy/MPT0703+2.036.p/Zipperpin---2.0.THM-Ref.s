%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xEUz25RhOx

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 104 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  451 (1007 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t176_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X23 @ ( k3_xboole_0 @ X24 @ X25 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X23 @ X24 ) @ ( k10_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t176_relat_1])).

thf('5',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t151_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X32 @ ( k10_relat_1 @ X33 @ X34 ) ) @ ( k10_relat_1 @ X33 @ ( k3_xboole_0 @ ( k9_relat_1 @ X33 @ X32 ) @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t151_funct_1])).

thf('12',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('14',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( k2_relat_1 @ X31 ) )
      | ( ( k9_relat_1 @ X31 @ ( k10_relat_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','18','19'])).

thf('21',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','20'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X26 @ ( k10_relat_1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('23',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X17 ) ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xEUz25RhOx
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 202 iterations in 0.069s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(t158_funct_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.21/0.50           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.21/0.50         ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.21/0.50              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.21/0.50            ( r1_tarski @ A @ B ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.21/0.50  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t28_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.21/0.50         (k10_relat_1 @ sk_C @ sk_B)) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(t176_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ C ) =>
% 0.21/0.50       ( r1_tarski @
% 0.21/0.50         ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.21/0.50         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.50         ((r1_tarski @ (k10_relat_1 @ X23 @ (k3_xboole_0 @ X24 @ X25)) @ 
% 0.21/0.50           (k3_xboole_0 @ (k10_relat_1 @ X23 @ X24) @ (k10_relat_1 @ X23 @ X25)))
% 0.21/0.50          | ~ (v1_relat_1 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [t176_relat_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.21/0.50         (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.21/0.50        (k10_relat_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.21/0.50           (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.50        | ((k10_relat_1 @ sk_C @ sk_A)
% 0.21/0.50            = (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.21/0.50         (k10_relat_1 @ sk_C @ sk_B)) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(t151_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ C ) =>
% 0.21/0.50       ( r1_tarski @
% 0.21/0.50         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ 
% 0.21/0.50         ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.50         ((r1_tarski @ (k3_xboole_0 @ X32 @ (k10_relat_1 @ X33 @ X34)) @ 
% 0.21/0.50           (k10_relat_1 @ X33 @ (k3_xboole_0 @ (k9_relat_1 @ X33 @ X32) @ X34)))
% 0.21/0.50          | ~ (v1_relat_1 @ X33))),
% 0.21/0.50      inference('cnf', [status(esa)], [t151_funct_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.21/0.50         (k10_relat_1 @ sk_C @ 
% 0.21/0.50          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 0.21/0.50           sk_B)))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t147_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.50         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X30 : $i, X31 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X30 @ (k2_relat_1 @ X31))
% 0.21/0.50          | ((k9_relat_1 @ X31 @ (k10_relat_1 @ X31 @ X30)) = (X30))
% 0.21/0.50          | ~ (v1_funct_1 @ X31)
% 0.21/0.50          | ~ (v1_relat_1 @ X31))),
% 0.21/0.50      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.50        | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.50  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.21/0.50        (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((k10_relat_1 @ sk_C @ sk_A)
% 0.21/0.50         = (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '20'])).
% 0.21/0.50  thf(t145_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X26 : $i, X27 : $i]:
% 0.21/0.50         ((r1_tarski @ (k9_relat_1 @ X26 @ (k10_relat_1 @ X26 @ X27)) @ X27)
% 0.21/0.50          | ~ (v1_funct_1 @ X26)
% 0.21/0.50          | ~ (v1_relat_1 @ X26))),
% 0.21/0.50      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (((r1_tarski @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 0.21/0.50         (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.50  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.21/0.50  thf(t17_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.21/0.50      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.21/0.50          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.50  thf(t12_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.50  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf(t31_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( r1_tarski @
% 0.21/0.50       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.21/0.50       ( k2_xboole_0 @ B @ C ) ))).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.50         (r1_tarski @ 
% 0.21/0.50          (k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k3_xboole_0 @ X15 @ X17)) @ 
% 0.21/0.50          (k2_xboole_0 @ X16 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.50      inference('sup+', [status(thm)], ['31', '39'])).
% 0.21/0.50  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
