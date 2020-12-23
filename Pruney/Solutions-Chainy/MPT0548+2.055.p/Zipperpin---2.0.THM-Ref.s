%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6m0UNtiOaQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:09 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 106 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  321 ( 551 expanded)
%              Number of equality atoms :   32 (  68 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X25 @ X26 ) @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) ) )
      | ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','6'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ k1_xboole_0 ) ) @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t54_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t54_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('20',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X17: $i] :
      ( ( ( k3_relat_1 @ X17 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('22',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t63_relat_1,axiom,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('23',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t63_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','5'])).

thf('28',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','26','27'])).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('29',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','6'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','5'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6m0UNtiOaQ
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:28:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 371 iterations in 0.166s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.43/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.61  thf(t88_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (![X25 : $i, X26 : $i]:
% 0.43/0.61         ((r1_tarski @ (k7_relat_1 @ X25 @ X26) @ X25) | ~ (v1_relat_1 @ X25))),
% 0.43/0.61      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.43/0.61  thf(t3_xboole_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ k1_xboole_0)
% 0.43/0.61          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.43/0.61  thf(t113_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.43/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.43/0.61          | ((X13) != (k1_xboole_0)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['3'])).
% 0.43/0.61  thf(fc6_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.43/0.61  thf('6', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '6'])).
% 0.43/0.61  thf(d1_xboole_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.61  thf(t86_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ C ) =>
% 0.43/0.61       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.43/0.61         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X22 @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X23)))
% 0.43/0.61          | (r2_hidden @ X22 @ X23)
% 0.43/0.61          | ~ (v1_relat_1 @ X24))),
% 0.43/0.61      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.43/0.61          | ~ (v1_relat_1 @ X1)
% 0.43/0.61          | (r2_hidden @ (sk_B @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r2_hidden @ (sk_B @ (k1_relat_1 @ k1_xboole_0)) @ X0)
% 0.43/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.43/0.61          | (v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0))))),
% 0.43/0.61      inference('sup+', [status(thm)], ['7', '10'])).
% 0.43/0.61  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '6'])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r2_hidden @ (sk_B @ (k1_relat_1 @ k1_xboole_0)) @ X0)
% 0.43/0.61          | (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.43/0.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.43/0.61  thf('15', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.43/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.43/0.61  thf(t54_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      (![X15 : $i, X16 : $i]:
% 0.43/0.61         (~ (r1_xboole_0 @ (k1_tarski @ X15) @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.43/0.61      inference('cnf', [status(esa)], [t54_zfmisc_1])).
% 0.43/0.61  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.43/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf('18', plain, ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '17'])).
% 0.43/0.61  thf(t6_boole, axiom,
% 0.43/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t6_boole])).
% 0.43/0.61  thf('20', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.43/0.61  thf(d6_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ( k3_relat_1 @ A ) =
% 0.43/0.61         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X17 : $i]:
% 0.43/0.61         (((k3_relat_1 @ X17)
% 0.43/0.61            = (k2_xboole_0 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.43/0.61          | ~ (v1_relat_1 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      ((((k3_relat_1 @ k1_xboole_0)
% 0.43/0.61          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 0.43/0.61        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.43/0.61  thf(t63_relat_1, axiom, (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.43/0.61  thf('23', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [t63_relat_1])).
% 0.43/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.43/0.61  thf('24', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.43/0.61  thf(t12_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i]:
% 0.43/0.61         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.43/0.61  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.61  thf('27', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf('28', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['22', '23', '26', '27'])).
% 0.43/0.61  thf(t150_relat_1, conjecture,
% 0.43/0.61    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.43/0.61  thf('29', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '6'])).
% 0.43/0.61  thf(t148_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (![X20 : $i, X21 : $i]:
% 0.43/0.61         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 0.43/0.61          | ~ (v1_relat_1 @ X20))),
% 0.43/0.61      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['30', '31'])).
% 0.43/0.61  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.43/0.61  thf('35', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['29', '34'])).
% 0.43/0.61  thf('36', plain, ($false),
% 0.43/0.61      inference('simplify_reflect-', [status(thm)], ['28', '35'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
