%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhJ8gOXRaV

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:30 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   69 (  81 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  653 ( 833 expanded)
%              Number of equality atoms :   47 (  59 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X26 @ X27 ) @ ( k10_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X23
       != ( k10_relat_1 @ X22 @ X21 ) )
      | ( r2_hidden @ X24 @ ( k1_relat_1 @ X22 ) )
      | ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('7',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k10_relat_1 @ X22 @ X21 ) )
      | ( r2_hidden @ X24 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k3_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k2_relat_1 @ X30 ) )
      | ( ( k9_relat_1 @ X30 @ ( k10_relat_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X18: $i] :
      ( ( ( k9_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_funct_1])).

thf('28',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','37','38','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhJ8gOXRaV
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:31:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.42/2.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.42/2.65  % Solved by: fo/fo7.sh
% 2.42/2.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.42/2.65  % done 2529 iterations in 2.187s
% 2.42/2.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.42/2.65  % SZS output start Refutation
% 2.42/2.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.42/2.65  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.42/2.65  thf(sk_B_type, type, sk_B: $i).
% 2.42/2.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.42/2.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.42/2.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.42/2.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.42/2.65  thf(sk_A_type, type, sk_A: $i).
% 2.42/2.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.42/2.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.42/2.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.42/2.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.42/2.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.42/2.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.42/2.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.42/2.65  thf(t169_relat_1, axiom,
% 2.42/2.65    (![A:$i]:
% 2.42/2.65     ( ( v1_relat_1 @ A ) =>
% 2.42/2.65       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.42/2.65  thf('0', plain,
% 2.42/2.65      (![X19 : $i]:
% 2.42/2.65         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 2.42/2.65          | ~ (v1_relat_1 @ X19))),
% 2.42/2.65      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.42/2.65  thf(t137_funct_1, axiom,
% 2.42/2.65    (![A:$i,B:$i,C:$i]:
% 2.42/2.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.42/2.65       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 2.42/2.65         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.42/2.65  thf('1', plain,
% 2.42/2.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.42/2.65         (((k10_relat_1 @ X26 @ (k3_xboole_0 @ X27 @ X28))
% 2.42/2.65            = (k3_xboole_0 @ (k10_relat_1 @ X26 @ X27) @ 
% 2.42/2.65               (k10_relat_1 @ X26 @ X28)))
% 2.42/2.65          | ~ (v1_funct_1 @ X26)
% 2.42/2.65          | ~ (v1_relat_1 @ X26))),
% 2.42/2.65      inference('cnf', [status(esa)], [t137_funct_1])).
% 2.42/2.65  thf('2', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (((k10_relat_1 @ X0 @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1))
% 2.42/2.65            = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))
% 2.42/2.65          | ~ (v1_relat_1 @ X0)
% 2.42/2.65          | ~ (v1_relat_1 @ X0)
% 2.42/2.65          | ~ (v1_funct_1 @ X0))),
% 2.42/2.65      inference('sup+', [status(thm)], ['0', '1'])).
% 2.42/2.65  thf('3', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (~ (v1_funct_1 @ X0)
% 2.42/2.65          | ~ (v1_relat_1 @ X0)
% 2.42/2.65          | ((k10_relat_1 @ X0 @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1))
% 2.42/2.65              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 2.42/2.65      inference('simplify', [status(thm)], ['2'])).
% 2.42/2.65  thf(d4_xboole_0, axiom,
% 2.42/2.65    (![A:$i,B:$i,C:$i]:
% 2.42/2.65     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.42/2.65       ( ![D:$i]:
% 2.42/2.65         ( ( r2_hidden @ D @ C ) <=>
% 2.42/2.65           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.42/2.65  thf('4', plain,
% 2.42/2.65      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.42/2.65         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.42/2.65          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.42/2.65          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.42/2.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.42/2.65  thf('5', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.42/2.65          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.42/2.65      inference('eq_fact', [status(thm)], ['4'])).
% 2.42/2.65  thf(d13_funct_1, axiom,
% 2.42/2.65    (![A:$i]:
% 2.42/2.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.42/2.65       ( ![B:$i,C:$i]:
% 2.42/2.65         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 2.42/2.65           ( ![D:$i]:
% 2.42/2.65             ( ( r2_hidden @ D @ C ) <=>
% 2.42/2.65               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 2.42/2.65                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 2.42/2.65  thf('6', plain,
% 2.42/2.65      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.42/2.65         (((X23) != (k10_relat_1 @ X22 @ X21))
% 2.42/2.65          | (r2_hidden @ X24 @ (k1_relat_1 @ X22))
% 2.42/2.65          | ~ (r2_hidden @ X24 @ X23)
% 2.42/2.65          | ~ (v1_funct_1 @ X22)
% 2.42/2.65          | ~ (v1_relat_1 @ X22))),
% 2.42/2.65      inference('cnf', [status(esa)], [d13_funct_1])).
% 2.42/2.65  thf('7', plain,
% 2.42/2.65      (![X21 : $i, X22 : $i, X24 : $i]:
% 2.42/2.65         (~ (v1_relat_1 @ X22)
% 2.42/2.65          | ~ (v1_funct_1 @ X22)
% 2.42/2.65          | ~ (r2_hidden @ X24 @ (k10_relat_1 @ X22 @ X21))
% 2.42/2.65          | (r2_hidden @ X24 @ (k1_relat_1 @ X22)))),
% 2.42/2.65      inference('simplify', [status(thm)], ['6'])).
% 2.42/2.65  thf('8', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.65         (((k10_relat_1 @ X1 @ X0)
% 2.42/2.65            = (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.42/2.65          | (r2_hidden @ 
% 2.42/2.65             (sk_D @ (k10_relat_1 @ X1 @ X0) @ (k10_relat_1 @ X1 @ X0) @ X2) @ 
% 2.42/2.65             (k1_relat_1 @ X1))
% 2.42/2.65          | ~ (v1_funct_1 @ X1)
% 2.42/2.65          | ~ (v1_relat_1 @ X1))),
% 2.42/2.65      inference('sup-', [status(thm)], ['5', '7'])).
% 2.42/2.65  thf('9', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.42/2.65          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.42/2.65      inference('eq_fact', [status(thm)], ['4'])).
% 2.42/2.65  thf('10', plain,
% 2.42/2.65      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.42/2.65         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.42/2.65          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.42/2.65          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.42/2.65          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.42/2.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.42/2.65  thf('11', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.42/2.65          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.42/2.65          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.42/2.65          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.42/2.65      inference('sup-', [status(thm)], ['9', '10'])).
% 2.42/2.65  thf('12', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.42/2.65          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.42/2.65          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.42/2.65      inference('simplify', [status(thm)], ['11'])).
% 2.42/2.65  thf('13', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.42/2.65          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.42/2.65      inference('eq_fact', [status(thm)], ['4'])).
% 2.42/2.65  thf('14', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.42/2.65          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 2.42/2.65      inference('clc', [status(thm)], ['12', '13'])).
% 2.42/2.65  thf('15', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (~ (v1_relat_1 @ X0)
% 2.42/2.65          | ~ (v1_funct_1 @ X0)
% 2.42/2.65          | ((k10_relat_1 @ X0 @ X1)
% 2.42/2.65              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))
% 2.42/2.65          | ((k10_relat_1 @ X0 @ X1)
% 2.42/2.65              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 2.42/2.65      inference('sup-', [status(thm)], ['8', '14'])).
% 2.42/2.65  thf('16', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (((k10_relat_1 @ X0 @ X1)
% 2.42/2.65            = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))
% 2.42/2.65          | ~ (v1_funct_1 @ X0)
% 2.42/2.65          | ~ (v1_relat_1 @ X0))),
% 2.42/2.65      inference('simplify', [status(thm)], ['15'])).
% 2.42/2.65  thf('17', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (((k10_relat_1 @ X1 @ X0)
% 2.42/2.65            = (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)))
% 2.42/2.65          | ~ (v1_relat_1 @ X1)
% 2.42/2.65          | ~ (v1_funct_1 @ X1)
% 2.42/2.65          | ~ (v1_relat_1 @ X1)
% 2.42/2.65          | ~ (v1_funct_1 @ X1))),
% 2.42/2.65      inference('sup+', [status(thm)], ['3', '16'])).
% 2.42/2.65  thf('18', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (~ (v1_funct_1 @ X1)
% 2.42/2.65          | ~ (v1_relat_1 @ X1)
% 2.42/2.65          | ((k10_relat_1 @ X1 @ X0)
% 2.42/2.65              = (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0))))),
% 2.42/2.65      inference('simplify', [status(thm)], ['17'])).
% 2.42/2.65  thf(d10_xboole_0, axiom,
% 2.42/2.65    (![A:$i,B:$i]:
% 2.42/2.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.42/2.65  thf('19', plain,
% 2.42/2.65      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 2.42/2.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.42/2.65  thf('20', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 2.42/2.65      inference('simplify', [status(thm)], ['19'])).
% 2.42/2.65  thf(t108_xboole_1, axiom,
% 2.42/2.65    (![A:$i,B:$i,C:$i]:
% 2.42/2.65     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 2.42/2.65  thf('21', plain,
% 2.42/2.65      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.42/2.65         (~ (r1_tarski @ X9 @ X10)
% 2.42/2.65          | (r1_tarski @ (k3_xboole_0 @ X9 @ X11) @ X10))),
% 2.42/2.65      inference('cnf', [status(esa)], [t108_xboole_1])).
% 2.42/2.65  thf('22', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 2.42/2.65      inference('sup-', [status(thm)], ['20', '21'])).
% 2.42/2.65  thf(t147_funct_1, axiom,
% 2.42/2.65    (![A:$i,B:$i]:
% 2.42/2.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.42/2.65       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 2.42/2.65         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.42/2.65  thf('23', plain,
% 2.42/2.65      (![X29 : $i, X30 : $i]:
% 2.42/2.65         (~ (r1_tarski @ X29 @ (k2_relat_1 @ X30))
% 2.42/2.65          | ((k9_relat_1 @ X30 @ (k10_relat_1 @ X30 @ X29)) = (X29))
% 2.42/2.65          | ~ (v1_funct_1 @ X30)
% 2.42/2.65          | ~ (v1_relat_1 @ X30))),
% 2.42/2.65      inference('cnf', [status(esa)], [t147_funct_1])).
% 2.42/2.65  thf('24', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (~ (v1_relat_1 @ X0)
% 2.42/2.65          | ~ (v1_funct_1 @ X0)
% 2.42/2.65          | ((k9_relat_1 @ X0 @ 
% 2.42/2.65              (k10_relat_1 @ X0 @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))
% 2.42/2.65              = (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))),
% 2.42/2.65      inference('sup-', [status(thm)], ['22', '23'])).
% 2.42/2.65  thf('25', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 2.42/2.65            = (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0))
% 2.42/2.65          | ~ (v1_relat_1 @ X1)
% 2.42/2.65          | ~ (v1_funct_1 @ X1)
% 2.42/2.65          | ~ (v1_funct_1 @ X1)
% 2.42/2.65          | ~ (v1_relat_1 @ X1))),
% 2.42/2.65      inference('sup+', [status(thm)], ['18', '24'])).
% 2.42/2.65  thf('26', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         (~ (v1_funct_1 @ X1)
% 2.42/2.65          | ~ (v1_relat_1 @ X1)
% 2.42/2.65          | ((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 2.42/2.65              = (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)))),
% 2.42/2.65      inference('simplify', [status(thm)], ['25'])).
% 2.42/2.65  thf(t146_relat_1, axiom,
% 2.42/2.65    (![A:$i]:
% 2.42/2.65     ( ( v1_relat_1 @ A ) =>
% 2.42/2.65       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.42/2.65  thf('27', plain,
% 2.42/2.65      (![X18 : $i]:
% 2.42/2.65         (((k9_relat_1 @ X18 @ (k1_relat_1 @ X18)) = (k2_relat_1 @ X18))
% 2.42/2.65          | ~ (v1_relat_1 @ X18))),
% 2.42/2.65      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.42/2.65  thf(t148_funct_1, conjecture,
% 2.42/2.65    (![A:$i,B:$i]:
% 2.42/2.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.42/2.65       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 2.42/2.65         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 2.42/2.65  thf(zf_stmt_0, negated_conjecture,
% 2.42/2.65    (~( ![A:$i,B:$i]:
% 2.42/2.65        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.42/2.65          ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 2.42/2.65            ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )),
% 2.42/2.65    inference('cnf.neg', [status(esa)], [t148_funct_1])).
% 2.42/2.65  thf('28', plain,
% 2.42/2.65      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 2.42/2.65         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 2.42/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.65  thf('29', plain,
% 2.42/2.65      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 2.42/2.65          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 2.42/2.65        | ~ (v1_relat_1 @ sk_B))),
% 2.42/2.65      inference('sup-', [status(thm)], ['27', '28'])).
% 2.42/2.65  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.65  thf('31', plain,
% 2.42/2.65      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 2.42/2.65         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 2.42/2.65      inference('demod', [status(thm)], ['29', '30'])).
% 2.42/2.65  thf('32', plain,
% 2.42/2.65      ((((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 2.42/2.65          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 2.42/2.65        | ~ (v1_relat_1 @ sk_B)
% 2.42/2.65        | ~ (v1_funct_1 @ sk_B))),
% 2.42/2.65      inference('sup-', [status(thm)], ['26', '31'])).
% 2.42/2.65  thf(commutativity_k2_tarski, axiom,
% 2.42/2.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.42/2.65  thf('33', plain,
% 2.42/2.65      (![X12 : $i, X13 : $i]:
% 2.42/2.65         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 2.42/2.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.42/2.65  thf(t12_setfam_1, axiom,
% 2.42/2.65    (![A:$i,B:$i]:
% 2.42/2.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.42/2.65  thf('34', plain,
% 2.42/2.65      (![X16 : $i, X17 : $i]:
% 2.42/2.65         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 2.42/2.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.42/2.65  thf('35', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]:
% 2.42/2.65         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 2.42/2.65      inference('sup+', [status(thm)], ['33', '34'])).
% 2.42/2.65  thf('36', plain,
% 2.42/2.65      (![X16 : $i, X17 : $i]:
% 2.42/2.65         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 2.42/2.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.42/2.65  thf('37', plain,
% 2.42/2.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.42/2.65      inference('sup+', [status(thm)], ['35', '36'])).
% 2.42/2.65  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.65  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 2.42/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.65  thf('40', plain,
% 2.42/2.65      (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))
% 2.42/2.65         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 2.42/2.65      inference('demod', [status(thm)], ['32', '37', '38', '39'])).
% 2.42/2.65  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 2.42/2.65  
% 2.42/2.65  % SZS output end Refutation
% 2.42/2.65  
% 2.42/2.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
