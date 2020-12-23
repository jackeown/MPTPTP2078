%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TJsqLBIi3z

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:42 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 130 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  564 (1178 expanded)
%              Number of equality atoms :   37 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k9_relat_1 @ X25 @ ( k3_xboole_0 @ X26 @ X27 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X25 @ X26 ) @ ( k9_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ X18 )
      | ( ( k4_xboole_0 @ X16 @ X18 )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','16'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('29',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( r1_tarski @ ( k10_relat_1 @ X30 @ ( k9_relat_1 @ X30 @ X31 ) ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('30',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( r1_tarski @ ( k10_relat_1 @ X30 @ ( k9_relat_1 @ X30 @ X31 ) ) @ X31 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('32',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( r1_tarski @ X28 @ ( k10_relat_1 @ X29 @ ( k9_relat_1 @ X29 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['30','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('57',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TJsqLBIi3z
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:26:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 221 iterations in 0.096s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.57  thf(t157_funct_1, conjecture,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.57       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.36/0.57           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.57         ( r1_tarski @ A @ B ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.57        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.57          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.36/0.57              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.57            ( r1_tarski @ A @ B ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.36/0.57  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t121_funct_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.57       ( ( v2_funct_1 @ C ) =>
% 0.36/0.57         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.36/0.57           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X25)
% 0.36/0.57          | ((k9_relat_1 @ X25 @ (k3_xboole_0 @ X26 @ X27))
% 0.36/0.57              = (k3_xboole_0 @ (k9_relat_1 @ X25 @ X26) @ 
% 0.36/0.57                 (k9_relat_1 @ X25 @ X27)))
% 0.36/0.57          | ~ (v1_funct_1 @ X25)
% 0.36/0.57          | ~ (v1_relat_1 @ X25))),
% 0.36/0.57      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(l32_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (![X5 : $i, X7 : $i]:
% 0.36/0.57         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.36/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      (((k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.36/0.57         = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.57  thf(t48_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (![X14 : $i, X15 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.36/0.57           = (k3_xboole_0 @ X14 @ X15))),
% 0.36/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (((k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ k1_xboole_0)
% 0.36/0.57         = (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.36/0.57            (k9_relat_1 @ sk_C @ sk_B)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.36/0.57  thf(t36_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.36/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.57  thf(t3_xboole_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (![X13 : $i]:
% 0.36/0.57         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.57  thf(t83_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X16 : $i, X18 : $i]:
% 0.36/0.57         ((r1_xboole_0 @ X16 @ X18) | ((k4_xboole_0 @ X16 @ X18) != (X16)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.57  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.36/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.57  thf(symmetry_r1_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.36/0.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.36/0.57  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (![X16 : $i, X17 : $i]:
% 0.36/0.57         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.36/0.57      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.57  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      (((k9_relat_1 @ sk_C @ sk_A)
% 0.36/0.57         = (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.36/0.57            (k9_relat_1 @ sk_C @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['6', '16'])).
% 0.36/0.57  thf(commutativity_k2_tarski, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      (![X19 : $i, X20 : $i]:
% 0.36/0.57         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.57  thf(t12_setfam_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (![X23 : $i, X24 : $i]:
% 0.36/0.57         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 0.36/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      (![X23 : $i, X24 : $i]:
% 0.36/0.57         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 0.36/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      (((k9_relat_1 @ sk_C @ sk_A)
% 0.36/0.57         = (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_B) @ 
% 0.36/0.57            (k9_relat_1 @ sk_C @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['17', '22'])).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      ((((k9_relat_1 @ sk_C @ sk_A)
% 0.36/0.57          = (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A)))
% 0.36/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.57      inference('sup+', [status(thm)], ['1', '23'])).
% 0.36/0.57  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('27', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('28', plain,
% 0.36/0.57      (((k9_relat_1 @ sk_C @ sk_A)
% 0.36/0.57         = (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.36/0.57  thf(t152_funct_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.57       ( ( v2_funct_1 @ B ) =>
% 0.36/0.57         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      (![X30 : $i, X31 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X30)
% 0.36/0.57          | (r1_tarski @ (k10_relat_1 @ X30 @ (k9_relat_1 @ X30 @ X31)) @ X31)
% 0.36/0.57          | ~ (v1_funct_1 @ X30)
% 0.36/0.57          | ~ (v1_relat_1 @ X30))),
% 0.36/0.57      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.36/0.57         (k3_xboole_0 @ sk_B @ sk_A))
% 0.36/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.57      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      (![X30 : $i, X31 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X30)
% 0.36/0.57          | (r1_tarski @ (k10_relat_1 @ X30 @ (k9_relat_1 @ X30 @ X31)) @ X31)
% 0.36/0.57          | ~ (v1_funct_1 @ X30)
% 0.36/0.57          | ~ (v1_relat_1 @ X30))),
% 0.36/0.57      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.36/0.57  thf('32', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t146_funct_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ B ) =>
% 0.36/0.57       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.57         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      (![X28 : $i, X29 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X28 @ (k1_relat_1 @ X29))
% 0.36/0.57          | (r1_tarski @ X28 @ (k10_relat_1 @ X29 @ (k9_relat_1 @ X29 @ X28)))
% 0.36/0.57          | ~ (v1_relat_1 @ X29))),
% 0.36/0.57      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.36/0.57  thf('34', plain,
% 0.36/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.57        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.57  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.57  thf(d10_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      (![X2 : $i, X4 : $i]:
% 0.36/0.57         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      ((~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_A)
% 0.36/0.57        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.57  thf('39', plain,
% 0.36/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.57        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['31', '38'])).
% 0.36/0.57  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('42', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.36/0.57  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('46', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('47', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['30', '43', '44', '45', '46'])).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.36/0.57  thf('49', plain,
% 0.36/0.57      (![X14 : $i, X15 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.36/0.57           = (k3_xboole_0 @ X14 @ X15))),
% 0.36/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.57  thf('50', plain,
% 0.36/0.57      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.36/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.57  thf('51', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.36/0.57      inference('sup+', [status(thm)], ['49', '50'])).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.57      inference('sup+', [status(thm)], ['48', '51'])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      (![X2 : $i, X4 : $i]:
% 0.36/0.57         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.57  thf('54', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.36/0.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.57  thf('55', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['47', '54'])).
% 0.36/0.57  thf('56', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.36/0.57      inference('sup+', [status(thm)], ['49', '50'])).
% 0.36/0.57  thf('57', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.36/0.57      inference('sup+', [status(thm)], ['55', '56'])).
% 0.36/0.57  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
