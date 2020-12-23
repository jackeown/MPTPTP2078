%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DT5rUnasLK

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 (  93 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   18
%              Number of atoms          :  452 ( 819 expanded)
%              Number of equality atoms :   49 (  96 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( ( k9_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('2',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k9_relat_1 @ X19 @ X20 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('6',plain,
    ( ( ( k2_relat_1 @ sk_B )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_relat_1 @ sk_B )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X15 @ X14 ) @ X14 )
      | ( X14
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('11',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k11_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ X16 @ ( k1_tarski @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('13',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k11_relat_1 @ X22 @ X23 ) )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( sk_C @ X15 @ X14 )
       != X15 )
      | ( X14
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','30'])).

thf('32',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['31'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k1_tarski @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['34','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DT5rUnasLK
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 81 iterations in 0.040s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(t14_funct_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.22/0.50         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.22/0.50            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.22/0.50  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t146_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X18 : $i]:
% 0.22/0.50         (((k9_relat_1 @ X18 @ (k1_relat_1 @ X18)) = (k2_relat_1 @ X18))
% 0.22/0.50          | ~ (v1_relat_1 @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(t151_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i]:
% 0.22/0.50         (((k9_relat_1 @ X19 @ X20) != (k1_xboole_0))
% 0.22/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X19) @ X20)
% 0.22/0.50          | ~ (v1_relat_1 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_B) != (k1_xboole_0))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.50        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('8', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_B) != (k1_xboole_0))
% 0.22/0.50        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.22/0.50  thf(t41_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (((X14) = (k1_xboole_0))
% 0.22/0.50          | (r2_hidden @ (sk_C @ X15 @ X14) @ X14)
% 0.22/0.50          | ((X14) = (k1_tarski @ X15)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(d16_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (((k11_relat_1 @ X16 @ X17) = (k9_relat_1 @ X16 @ (k1_tarski @ X17)))
% 0.22/0.50          | ~ (v1_relat_1 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf(t204_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ C ) =>
% 0.22/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X21 @ (k11_relat_1 @ X22 @ X23))
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X23 @ X21) @ X22)
% 0.22/0.50          | ~ (v1_relat_1 @ X22))),
% 0.22/0.50      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.22/0.50          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.50          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '19'])).
% 0.22/0.50  thf(t8_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.50           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.50         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.22/0.50          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.22/0.50          | ~ (v1_funct_1 @ X25)
% 0.22/0.50          | ~ (v1_relat_1 @ X25))),
% 0.22/0.50      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.50          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.50          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (((X14) = (k1_xboole_0))
% 0.22/0.50          | ((sk_C @ X15 @ X14) != (X15))
% 0.22/0.50          | ((X14) = (k1_tarski @ X15)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.22/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.50          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.50          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.22/0.50          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.22/0.50        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('30', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.50        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '30'])).
% 0.22/0.50  thf('32', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.50  thf(l24_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i]:
% 0.22/0.50         (~ (r1_xboole_0 @ (k1_tarski @ X12) @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.22/0.50  thf('34', plain, (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.50      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.50  thf(l1_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         ((r2_hidden @ X9 @ X10) | ~ (r1_tarski @ (k1_tarski @ X9) @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.50  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain, ($false), inference('demod', [status(thm)], ['34', '38'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
