%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0VZggOQENQ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 110 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  483 (1052 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('1',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','11'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k9_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X17 @ X18 ) @ ( k9_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('14',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( r1_tarski @ ( k10_relat_1 @ X22 @ ( k9_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( r1_tarski @ ( k10_relat_1 @ X22 @ ( k9_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( r1_tarski @ X20 @ ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0VZggOQENQ
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 88 iterations in 0.043s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(t157_funct_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.20/0.49           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.20/0.49         ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.20/0.49              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.20/0.49            ( r1_tarski @ A @ B ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.20/0.49  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l32_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X3 : $i, X5 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.20/0.49         = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(t48_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.20/0.49           = (k3_xboole_0 @ X9 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ k1_xboole_0)
% 0.20/0.49         = (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.20/0.49            (k9_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf(t3_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.49  thf('6', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.49  thf(commutativity_k2_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.49  thf(t12_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((k9_relat_1 @ sk_C @ sk_A)
% 0.20/0.49         = (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_B) @ 
% 0.20/0.49            (k9_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6', '11'])).
% 0.20/0.49  thf(t121_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49       ( ( v2_funct_1 @ C ) =>
% 0.20/0.49         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.20/0.49           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.49         (~ (v2_funct_1 @ X17)
% 0.20/0.49          | ((k9_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19))
% 0.20/0.49              = (k3_xboole_0 @ (k9_relat_1 @ X17 @ X18) @ 
% 0.20/0.49                 (k9_relat_1 @ X17 @ X19)))
% 0.20/0.49          | ~ (v1_funct_1 @ X17)
% 0.20/0.49          | ~ (v1_relat_1 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((((k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.20/0.49          = (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.49      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.20/0.49         = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.20/0.49  thf(t152_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( v2_funct_1 @ B ) =>
% 0.20/0.49         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i]:
% 0.20/0.49         (~ (v2_funct_1 @ X22)
% 0.20/0.49          | (r1_tarski @ (k10_relat_1 @ X22 @ (k9_relat_1 @ X22 @ X23)) @ X23)
% 0.20/0.49          | ~ (v1_funct_1 @ X22)
% 0.20/0.49          | ~ (v1_relat_1 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.20/0.49         (k3_xboole_0 @ sk_B @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.49      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.20/0.49        (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i]:
% 0.20/0.49         (~ (v2_funct_1 @ X22)
% 0.20/0.49          | (r1_tarski @ (k10_relat_1 @ X22 @ (k9_relat_1 @ X22 @ X23)) @ X23)
% 0.20/0.49          | ~ (v1_funct_1 @ X22)
% 0.20/0.49          | ~ (v1_relat_1 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.20/0.49  thf('26', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t146_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.49         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.20/0.49          | (r1_tarski @ X20 @ (k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X20)))
% 0.20/0.49          | ~ (v1_relat_1 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_A)
% 0.20/0.49        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.49        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '32'])).
% 0.20/0.49  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.20/0.49  thf('38', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(t17_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.49      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.49          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.49  thf('46', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.49      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
