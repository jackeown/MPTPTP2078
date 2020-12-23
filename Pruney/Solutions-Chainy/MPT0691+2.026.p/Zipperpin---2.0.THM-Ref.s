%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eCXvmh7FfO

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:21 EST 2020

% Result     : Theorem 5.63s
% Output     : Refutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 111 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   21
%              Number of atoms          :  614 ( 914 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k3_xboole_0 @ X41 @ ( k10_relat_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X32: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X33 @ X34 ) @ ( k10_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X1 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k3_xboole_0 @ X41 @ ( k10_relat_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','34'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('36',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) ) @ X38 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('37',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) )
        = ( k9_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eCXvmh7FfO
% 0.16/0.37  % Computer   : n005.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:13:03 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 5.63/5.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.63/5.81  % Solved by: fo/fo7.sh
% 5.63/5.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.63/5.81  % done 9505 iterations in 5.339s
% 5.63/5.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.63/5.81  % SZS output start Refutation
% 5.63/5.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.63/5.81  thf(sk_B_type, type, sk_B: $i).
% 5.63/5.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.63/5.81  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.63/5.81  thf(sk_A_type, type, sk_A: $i).
% 5.63/5.81  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 5.63/5.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.63/5.81  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.63/5.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.63/5.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.63/5.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.63/5.81  thf(t146_funct_1, conjecture,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( v1_relat_1 @ B ) =>
% 5.63/5.81       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 5.63/5.81         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 5.63/5.81  thf(zf_stmt_0, negated_conjecture,
% 5.63/5.81    (~( ![A:$i,B:$i]:
% 5.63/5.81        ( ( v1_relat_1 @ B ) =>
% 5.63/5.81          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 5.63/5.81            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 5.63/5.81    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 5.63/5.81  thf('0', plain,
% 5.63/5.81      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf(t139_funct_1, axiom,
% 5.63/5.81    (![A:$i,B:$i,C:$i]:
% 5.63/5.81     ( ( v1_relat_1 @ C ) =>
% 5.63/5.81       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 5.63/5.81         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 5.63/5.81  thf('1', plain,
% 5.63/5.81      (![X41 : $i, X42 : $i, X43 : $i]:
% 5.63/5.81         (((k10_relat_1 @ (k7_relat_1 @ X42 @ X41) @ X43)
% 5.63/5.81            = (k3_xboole_0 @ X41 @ (k10_relat_1 @ X42 @ X43)))
% 5.63/5.81          | ~ (v1_relat_1 @ X42))),
% 5.63/5.81      inference('cnf', [status(esa)], [t139_funct_1])).
% 5.63/5.81  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf(t28_xboole_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.63/5.81  thf('3', plain,
% 5.63/5.81      (![X19 : $i, X20 : $i]:
% 5.63/5.81         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 5.63/5.81      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.63/5.81  thf('4', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 5.63/5.81      inference('sup-', [status(thm)], ['2', '3'])).
% 5.63/5.81  thf(t169_relat_1, axiom,
% 5.63/5.81    (![A:$i]:
% 5.63/5.81     ( ( v1_relat_1 @ A ) =>
% 5.63/5.81       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 5.63/5.81  thf('5', plain,
% 5.63/5.81      (![X32 : $i]:
% 5.63/5.81         (((k10_relat_1 @ X32 @ (k2_relat_1 @ X32)) = (k1_relat_1 @ X32))
% 5.63/5.81          | ~ (v1_relat_1 @ X32))),
% 5.63/5.81      inference('cnf', [status(esa)], [t169_relat_1])).
% 5.63/5.81  thf(t170_relat_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( v1_relat_1 @ B ) =>
% 5.63/5.81       ( r1_tarski @
% 5.63/5.81         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 5.63/5.81  thf('6', plain,
% 5.63/5.81      (![X33 : $i, X34 : $i]:
% 5.63/5.81         ((r1_tarski @ (k10_relat_1 @ X33 @ X34) @ 
% 5.63/5.81           (k10_relat_1 @ X33 @ (k2_relat_1 @ X33)))
% 5.63/5.81          | ~ (v1_relat_1 @ X33))),
% 5.63/5.81      inference('cnf', [status(esa)], [t170_relat_1])).
% 5.63/5.81  thf('7', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 5.63/5.81           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 5.63/5.81          | ~ (v1_relat_1 @ X0)
% 5.63/5.81          | ~ (v1_relat_1 @ X0))),
% 5.63/5.81      inference('sup+', [status(thm)], ['5', '6'])).
% 5.63/5.81  thf('8', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (~ (v1_relat_1 @ X0)
% 5.63/5.81          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 5.63/5.81             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 5.63/5.81      inference('simplify', [status(thm)], ['7'])).
% 5.63/5.81  thf(commutativity_k3_xboole_0, axiom,
% 5.63/5.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.63/5.81  thf('9', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.63/5.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.63/5.81  thf('10', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf(t108_xboole_1, axiom,
% 5.63/5.81    (![A:$i,B:$i,C:$i]:
% 5.63/5.81     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 5.63/5.81  thf('11', plain,
% 5.63/5.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 5.63/5.81         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 5.63/5.81      inference('cnf', [status(esa)], [t108_xboole_1])).
% 5.63/5.81  thf('12', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))),
% 5.63/5.81      inference('sup-', [status(thm)], ['10', '11'])).
% 5.63/5.81  thf('13', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 5.63/5.81      inference('sup+', [status(thm)], ['9', '12'])).
% 5.63/5.81  thf(t12_xboole_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.63/5.81  thf('14', plain,
% 5.63/5.81      (![X14 : $i, X15 : $i]:
% 5.63/5.81         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 5.63/5.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.63/5.81  thf('15', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ (k1_relat_1 @ sk_B))
% 5.63/5.81           = (k1_relat_1 @ sk_B))),
% 5.63/5.81      inference('sup-', [status(thm)], ['13', '14'])).
% 5.63/5.81  thf(t167_relat_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( v1_relat_1 @ B ) =>
% 5.63/5.81       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 5.63/5.81  thf('16', plain,
% 5.63/5.81      (![X30 : $i, X31 : $i]:
% 5.63/5.81         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 5.63/5.81          | ~ (v1_relat_1 @ X30))),
% 5.63/5.81      inference('cnf', [status(esa)], [t167_relat_1])).
% 5.63/5.81  thf(t10_xboole_1, axiom,
% 5.63/5.81    (![A:$i,B:$i,C:$i]:
% 5.63/5.81     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 5.63/5.81  thf('17', plain,
% 5.63/5.81      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.63/5.81         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 5.63/5.81      inference('cnf', [status(esa)], [t10_xboole_1])).
% 5.63/5.81  thf('18', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.81         (~ (v1_relat_1 @ X0)
% 5.63/5.81          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 5.63/5.81             (k2_xboole_0 @ X2 @ (k1_relat_1 @ X0))))),
% 5.63/5.81      inference('sup-', [status(thm)], ['16', '17'])).
% 5.63/5.81  thf('19', plain,
% 5.63/5.81      (![X1 : $i]:
% 5.63/5.81         ((r1_tarski @ (k10_relat_1 @ sk_B @ X1) @ (k1_relat_1 @ sk_B))
% 5.63/5.81          | ~ (v1_relat_1 @ sk_B))),
% 5.63/5.81      inference('sup+', [status(thm)], ['15', '18'])).
% 5.63/5.81  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('21', plain,
% 5.63/5.81      (![X1 : $i]:
% 5.63/5.81         (r1_tarski @ (k10_relat_1 @ sk_B @ X1) @ (k1_relat_1 @ sk_B))),
% 5.63/5.81      inference('demod', [status(thm)], ['19', '20'])).
% 5.63/5.81  thf(d10_xboole_0, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.63/5.81  thf('22', plain,
% 5.63/5.81      (![X2 : $i, X4 : $i]:
% 5.63/5.81         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 5.63/5.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.63/5.81  thf('23', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 5.63/5.81          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 5.63/5.81      inference('sup-', [status(thm)], ['21', '22'])).
% 5.63/5.81  thf('24', plain,
% 5.63/5.81      ((~ (v1_relat_1 @ sk_B)
% 5.63/5.81        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 5.63/5.81      inference('sup-', [status(thm)], ['8', '23'])).
% 5.63/5.81  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('26', plain,
% 5.63/5.81      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 5.63/5.81      inference('demod', [status(thm)], ['24', '25'])).
% 5.63/5.81  thf('27', plain,
% 5.63/5.81      (![X41 : $i, X42 : $i, X43 : $i]:
% 5.63/5.81         (((k10_relat_1 @ (k7_relat_1 @ X42 @ X41) @ X43)
% 5.63/5.81            = (k3_xboole_0 @ X41 @ (k10_relat_1 @ X42 @ X43)))
% 5.63/5.81          | ~ (v1_relat_1 @ X42))),
% 5.63/5.81      inference('cnf', [status(esa)], [t139_funct_1])).
% 5.63/5.81  thf('28', plain,
% 5.63/5.81      (![X30 : $i, X31 : $i]:
% 5.63/5.81         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 5.63/5.81          | ~ (v1_relat_1 @ X30))),
% 5.63/5.81      inference('cnf', [status(esa)], [t167_relat_1])).
% 5.63/5.81  thf('29', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.81         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 5.63/5.81           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 5.63/5.81          | ~ (v1_relat_1 @ X1)
% 5.63/5.81          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 5.63/5.81      inference('sup+', [status(thm)], ['27', '28'])).
% 5.63/5.81  thf(dt_k7_relat_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 5.63/5.81  thf('30', plain,
% 5.63/5.81      (![X26 : $i, X27 : $i]:
% 5.63/5.81         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k7_relat_1 @ X26 @ X27)))),
% 5.63/5.81      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.63/5.81  thf('31', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.81         (~ (v1_relat_1 @ X1)
% 5.63/5.81          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 5.63/5.81             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 5.63/5.81      inference('clc', [status(thm)], ['29', '30'])).
% 5.63/5.81  thf('32', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 5.63/5.81           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 5.63/5.81          | ~ (v1_relat_1 @ sk_B))),
% 5.63/5.81      inference('sup+', [status(thm)], ['26', '31'])).
% 5.63/5.81  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('34', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 5.63/5.81          (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 5.63/5.81      inference('demod', [status(thm)], ['32', '33'])).
% 5.63/5.81  thf('35', plain,
% 5.63/5.81      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 5.63/5.81      inference('sup+', [status(thm)], ['4', '34'])).
% 5.63/5.81  thf(t87_relat_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( v1_relat_1 @ B ) =>
% 5.63/5.81       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 5.63/5.81  thf('36', plain,
% 5.63/5.81      (![X37 : $i, X38 : $i]:
% 5.63/5.81         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X37 @ X38)) @ X38)
% 5.63/5.81          | ~ (v1_relat_1 @ X37))),
% 5.63/5.81      inference('cnf', [status(esa)], [t87_relat_1])).
% 5.63/5.81  thf('37', plain,
% 5.63/5.81      (![X2 : $i, X4 : $i]:
% 5.63/5.81         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 5.63/5.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.63/5.81  thf('38', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i]:
% 5.63/5.81         (~ (v1_relat_1 @ X1)
% 5.63/5.81          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 5.63/5.81          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 5.63/5.81      inference('sup-', [status(thm)], ['36', '37'])).
% 5.63/5.81  thf('39', plain,
% 5.63/5.81      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 5.63/5.81        | ~ (v1_relat_1 @ sk_B))),
% 5.63/5.81      inference('sup-', [status(thm)], ['35', '38'])).
% 5.63/5.81  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('41', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 5.63/5.81      inference('demod', [status(thm)], ['39', '40'])).
% 5.63/5.81  thf(t148_relat_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( v1_relat_1 @ B ) =>
% 5.63/5.81       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 5.63/5.81  thf('42', plain,
% 5.63/5.81      (![X28 : $i, X29 : $i]:
% 5.63/5.81         (((k2_relat_1 @ (k7_relat_1 @ X28 @ X29)) = (k9_relat_1 @ X28 @ X29))
% 5.63/5.81          | ~ (v1_relat_1 @ X28))),
% 5.63/5.81      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.63/5.81  thf('43', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (~ (v1_relat_1 @ X0)
% 5.63/5.81          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 5.63/5.81             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 5.63/5.81      inference('simplify', [status(thm)], ['7'])).
% 5.63/5.81  thf('44', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i]:
% 5.63/5.81         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 5.63/5.81           (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 5.63/5.81          | ~ (v1_relat_1 @ X1)
% 5.63/5.81          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 5.63/5.81      inference('sup+', [status(thm)], ['42', '43'])).
% 5.63/5.81  thf('45', plain,
% 5.63/5.81      (![X26 : $i, X27 : $i]:
% 5.63/5.81         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k7_relat_1 @ X26 @ X27)))),
% 5.63/5.81      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.63/5.81  thf('46', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i]:
% 5.63/5.81         (~ (v1_relat_1 @ X1)
% 5.63/5.81          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 5.63/5.81             (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))))),
% 5.63/5.81      inference('clc', [status(thm)], ['44', '45'])).
% 5.63/5.81  thf('47', plain,
% 5.63/5.81      (((r1_tarski @ sk_A @ 
% 5.63/5.81         (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))
% 5.63/5.81        | ~ (v1_relat_1 @ sk_B))),
% 5.63/5.81      inference('sup+', [status(thm)], ['41', '46'])).
% 5.63/5.81  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('49', plain,
% 5.63/5.81      ((r1_tarski @ sk_A @ 
% 5.63/5.81        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 5.63/5.81      inference('demod', [status(thm)], ['47', '48'])).
% 5.63/5.81  thf('50', plain,
% 5.63/5.81      (((r1_tarski @ sk_A @ 
% 5.63/5.81         (k3_xboole_0 @ sk_A @ 
% 5.63/5.81          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 5.63/5.81        | ~ (v1_relat_1 @ sk_B))),
% 5.63/5.81      inference('sup+', [status(thm)], ['1', '49'])).
% 5.63/5.81  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('52', plain,
% 5.63/5.81      ((r1_tarski @ sk_A @ 
% 5.63/5.81        (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 5.63/5.81      inference('demod', [status(thm)], ['50', '51'])).
% 5.63/5.81  thf('53', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.63/5.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.63/5.81  thf(t18_xboole_1, axiom,
% 5.63/5.81    (![A:$i,B:$i,C:$i]:
% 5.63/5.81     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 5.63/5.81  thf('54', plain,
% 5.63/5.81      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.63/5.81         ((r1_tarski @ X16 @ X17)
% 5.63/5.81          | ~ (r1_tarski @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 5.63/5.81      inference('cnf', [status(esa)], [t18_xboole_1])).
% 5.63/5.81  thf('55', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.81         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['53', '54'])).
% 5.63/5.81  thf('56', plain,
% 5.63/5.81      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 5.63/5.81      inference('sup-', [status(thm)], ['52', '55'])).
% 5.63/5.81  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 5.63/5.81  
% 5.63/5.81  % SZS output end Refutation
% 5.63/5.81  
% 5.63/5.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
