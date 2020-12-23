%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EPGPFbmIwF

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   62 (  98 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  448 (1155 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( r1_tarski @ ( k10_relat_1 @ X12 @ ( k9_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('5',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k9_relat_1 @ X8 @ X6 ) @ ( k9_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r1_tarski @ X10 @ ( k10_relat_1 @ X11 @ ( k9_relat_1 @ X11 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( r1_tarski @ ( k10_relat_1 @ X12 @ ( k9_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['23','36','37','38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EPGPFbmIwF
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 161 iterations in 0.107s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(t157_funct_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.55       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.37/0.55           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.37/0.55         ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.55          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.37/0.55              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.37/0.55            ( r1_tarski @ A @ B ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.37/0.55  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t155_funct_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.55       ( ( v2_funct_1 @ B ) =>
% 0.37/0.55         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i]:
% 0.37/0.55         (~ (v2_funct_1 @ X14)
% 0.37/0.55          | ((k10_relat_1 @ X14 @ X15)
% 0.37/0.55              = (k9_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 0.37/0.55          | ~ (v1_funct_1 @ X14)
% 0.37/0.55          | ~ (v1_relat_1 @ X14))),
% 0.37/0.55      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.37/0.55  thf(dt_k2_funct_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X9 : $i]:
% 0.37/0.55         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.37/0.55          | ~ (v1_funct_1 @ X9)
% 0.37/0.55          | ~ (v1_relat_1 @ X9))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.55  thf(t152_funct_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.55       ( ( v2_funct_1 @ B ) =>
% 0.37/0.55         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         (~ (v2_funct_1 @ X12)
% 0.37/0.55          | (r1_tarski @ (k10_relat_1 @ X12 @ (k9_relat_1 @ X12 @ X13)) @ X13)
% 0.37/0.55          | ~ (v1_funct_1 @ X12)
% 0.37/0.55          | ~ (v1_relat_1 @ X12))),
% 0.37/0.55      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i]:
% 0.37/0.55         (~ (v2_funct_1 @ X14)
% 0.37/0.55          | ((k10_relat_1 @ X14 @ X15)
% 0.37/0.55              = (k9_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 0.37/0.55          | ~ (v1_funct_1 @ X14)
% 0.37/0.55          | ~ (v1_relat_1 @ X14))),
% 0.37/0.55      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t156_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ C ) =>
% 0.37/0.55       ( ( r1_tarski @ A @ B ) =>
% 0.37/0.55         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X6 @ X7)
% 0.37/0.55          | ~ (v1_relat_1 @ X8)
% 0.37/0.55          | (r1_tarski @ (k9_relat_1 @ X8 @ X6) @ (k9_relat_1 @ X8 @ X7)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r1_tarski @ (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.37/0.55           (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf(t1_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.55       ( r1_tarski @ A @ C ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X3 @ X4)
% 0.37/0.55          | ~ (r1_tarski @ X4 @ X5)
% 0.37/0.55          | (r1_tarski @ X3 @ X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X0)
% 0.37/0.55          | (r1_tarski @ (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ X1)
% 0.37/0.55          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)) @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)) @ X1)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (v2_funct_1 @ X0)
% 0.37/0.55          | (r1_tarski @ 
% 0.37/0.55             (k9_relat_1 @ (k2_funct_1 @ X0) @ (k9_relat_1 @ sk_C @ sk_A)) @ X1)
% 0.37/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.55        | (r1_tarski @ 
% 0.37/0.55           (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.37/0.55           sk_B)
% 0.37/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '10'])).
% 0.37/0.55  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('14', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('15', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.55        | (r1_tarski @ 
% 0.37/0.55           (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.37/0.55           sk_B))),
% 0.37/0.55      inference('demod', [status(thm)],
% 0.37/0.55                ['11', '12', '13', '14', '15', '16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | (r1_tarski @ 
% 0.37/0.55           (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.37/0.55           sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['2', '18'])).
% 0.37/0.55  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      ((r1_tarski @ 
% 0.37/0.55        (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_B)),
% 0.37/0.55      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_B)
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.55      inference('sup+', [status(thm)], ['1', '22'])).
% 0.37/0.55  thf('24', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t146_funct_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ B ) =>
% 0.37/0.55       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.55         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X10 @ (k1_relat_1 @ X11))
% 0.37/0.55          | (r1_tarski @ X10 @ (k10_relat_1 @ X11 @ (k9_relat_1 @ X11 @ X10)))
% 0.37/0.55          | ~ (v1_relat_1 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.55  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         (~ (v2_funct_1 @ X12)
% 0.37/0.55          | (r1_tarski @ (k10_relat_1 @ X12 @ (k9_relat_1 @ X12 @ X13)) @ X13)
% 0.37/0.55          | ~ (v1_funct_1 @ X12)
% 0.37/0.55          | ~ (v1_relat_1 @ X12))),
% 0.37/0.55      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.37/0.55  thf(d10_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X0 : $i, X2 : $i]:
% 0.37/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X1)
% 0.37/0.55          | ~ (v1_funct_1 @ X1)
% 0.37/0.55          | ~ (v2_funct_1 @ X1)
% 0.37/0.55          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.37/0.55          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      ((((sk_A) = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.37/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '31'])).
% 0.37/0.55  thf('33', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (((sk_A) = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.37/0.55  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('40', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.55      inference('demod', [status(thm)], ['23', '36', '37', '38', '39'])).
% 0.37/0.55  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
