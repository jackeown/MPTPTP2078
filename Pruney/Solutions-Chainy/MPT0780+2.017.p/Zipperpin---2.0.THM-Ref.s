%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QawdbaStRv

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:27 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 110 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :   19
%              Number of atoms          :  629 ( 935 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t19_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k3_relat_1 @ ( k2_wellord1 @ X32 @ X33 ) ) )
      | ( r2_hidden @ X31 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k8_relat_1 @ X24 @ X23 )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X34 @ X36 ) @ X35 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X34 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('27',plain,(
    ! [X22: $i] :
      ( ( ( k3_relat_1 @ X22 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('35',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k7_relat_1 @ X25 @ X26 )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_wellord1 @ X30 @ X29 )
        = ( k8_relat_1 @ X29 @ ( k7_relat_1 @ X30 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C_1 @ sk_A ) )
     != ( k2_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C_1 @ sk_A ) )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_wellord1 @ sk_C_1 @ sk_A )
     != ( k2_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k2_wellord1 @ sk_C_1 @ sk_A )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QawdbaStRv
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.35/1.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.35/1.57  % Solved by: fo/fo7.sh
% 1.35/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.57  % done 1209 iterations in 1.130s
% 1.35/1.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.35/1.57  % SZS output start Refutation
% 1.35/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.57  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.35/1.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.57  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 1.35/1.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.35/1.57  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.35/1.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.35/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.35/1.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.35/1.57  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.35/1.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.35/1.57  thf(d3_tarski, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( r1_tarski @ A @ B ) <=>
% 1.35/1.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.35/1.57  thf('0', plain,
% 1.35/1.57      (![X1 : $i, X3 : $i]:
% 1.35/1.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.35/1.57  thf(t19_wellord1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ C ) =>
% 1.35/1.57       ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) ) =>
% 1.35/1.57         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) ) ))).
% 1.35/1.57  thf('1', plain,
% 1.35/1.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.35/1.57         (~ (r2_hidden @ X31 @ (k3_relat_1 @ (k2_wellord1 @ X32 @ X33)))
% 1.35/1.57          | (r2_hidden @ X31 @ X33)
% 1.35/1.57          | ~ (v1_relat_1 @ X32))),
% 1.35/1.57      inference('cnf', [status(esa)], [t19_wellord1])).
% 1.35/1.57  thf('2', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 1.35/1.57          | ~ (v1_relat_1 @ X1)
% 1.35/1.57          | (r2_hidden @ 
% 1.35/1.57             (sk_C @ X2 @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0))) @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['0', '1'])).
% 1.35/1.57  thf(t29_wellord1, conjecture,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ C ) =>
% 1.35/1.57       ( ( r1_tarski @ A @ B ) =>
% 1.35/1.57         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 1.35/1.57           ( k2_wellord1 @ C @ A ) ) ) ))).
% 1.35/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.57    (~( ![A:$i,B:$i,C:$i]:
% 1.35/1.57        ( ( v1_relat_1 @ C ) =>
% 1.35/1.57          ( ( r1_tarski @ A @ B ) =>
% 1.35/1.57            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 1.35/1.57              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 1.35/1.57    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 1.35/1.57  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('4', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         (~ (r2_hidden @ X0 @ X1)
% 1.35/1.57          | (r2_hidden @ X0 @ X2)
% 1.35/1.57          | ~ (r1_tarski @ X1 @ X2))),
% 1.35/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.35/1.57  thf('5', plain,
% 1.35/1.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['3', '4'])).
% 1.35/1.57  thf('6', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ X1)
% 1.35/1.57          | (r2_hidden @ 
% 1.35/1.57             (sk_C @ X1 @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A))) @ sk_B))),
% 1.35/1.57      inference('sup-', [status(thm)], ['2', '5'])).
% 1.35/1.57  thf('7', plain,
% 1.35/1.57      (![X1 : $i, X3 : $i]:
% 1.35/1.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.35/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.35/1.57  thf('8', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B))),
% 1.35/1.57      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.57  thf('9', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B))),
% 1.35/1.57      inference('simplify', [status(thm)], ['8'])).
% 1.35/1.57  thf(d6_relat_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ A ) =>
% 1.35/1.57       ( ( k3_relat_1 @ A ) =
% 1.35/1.57         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.35/1.57  thf('10', plain,
% 1.35/1.57      (![X22 : $i]:
% 1.35/1.57         (((k3_relat_1 @ X22)
% 1.35/1.57            = (k2_xboole_0 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 1.35/1.57          | ~ (v1_relat_1 @ X22))),
% 1.35/1.57      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.35/1.57  thf(d10_xboole_0, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.35/1.57  thf('11', plain,
% 1.35/1.57      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.35/1.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.57  thf('12', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.35/1.57      inference('simplify', [status(thm)], ['11'])).
% 1.35/1.57  thf(t10_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.35/1.57  thf('13', plain,
% 1.35/1.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.35/1.57         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ X7 @ (k2_xboole_0 @ X9 @ X8)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.35/1.57  thf('14', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['12', '13'])).
% 1.35/1.57  thf(t1_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.35/1.57       ( r1_tarski @ A @ C ) ))).
% 1.35/1.57  thf('15', plain,
% 1.35/1.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.35/1.57         (~ (r1_tarski @ X10 @ X11)
% 1.35/1.57          | ~ (r1_tarski @ X11 @ X12)
% 1.35/1.57          | (r1_tarski @ X10 @ X12))),
% 1.35/1.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.35/1.57  thf('16', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.35/1.57      inference('sup-', [status(thm)], ['14', '15'])).
% 1.35/1.57  thf('17', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['10', '16'])).
% 1.35/1.57  thf('18', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['9', '17'])).
% 1.35/1.57  thf(dt_k2_wellord1, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 1.35/1.57  thf('19', plain,
% 1.35/1.57      (![X27 : $i, X28 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k2_wellord1 @ X27 @ X28)))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.35/1.57  thf('20', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.35/1.57          | ~ (v1_relat_1 @ X0))),
% 1.35/1.57      inference('clc', [status(thm)], ['18', '19'])).
% 1.35/1.57  thf(t125_relat_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ B ) =>
% 1.35/1.57       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.35/1.57         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 1.35/1.57  thf('21', plain,
% 1.35/1.57      (![X23 : $i, X24 : $i]:
% 1.35/1.57         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 1.35/1.57          | ((k8_relat_1 @ X24 @ X23) = (X23))
% 1.35/1.57          | ~ (v1_relat_1 @ X23))),
% 1.35/1.57      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.35/1.57  thf('22', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 1.35/1.57          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 1.35/1.57              = (k2_wellord1 @ X0 @ sk_A)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['20', '21'])).
% 1.35/1.57  thf('23', plain,
% 1.35/1.57      (![X27 : $i, X28 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k2_wellord1 @ X27 @ X28)))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.35/1.57  thf('24', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 1.35/1.57            = (k2_wellord1 @ X0 @ sk_A))
% 1.35/1.57          | ~ (v1_relat_1 @ X0))),
% 1.35/1.57      inference('clc', [status(thm)], ['22', '23'])).
% 1.35/1.57  thf(t27_wellord1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ C ) =>
% 1.35/1.57       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 1.35/1.57         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 1.35/1.57  thf('25', plain,
% 1.35/1.57      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.35/1.57         (((k2_wellord1 @ (k2_wellord1 @ X34 @ X36) @ X35)
% 1.35/1.57            = (k2_wellord1 @ (k2_wellord1 @ X34 @ X35) @ X36))
% 1.35/1.57          | ~ (v1_relat_1 @ X34))),
% 1.35/1.57      inference('cnf', [status(esa)], [t27_wellord1])).
% 1.35/1.57  thf('26', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B))),
% 1.35/1.57      inference('simplify', [status(thm)], ['8'])).
% 1.35/1.57  thf('27', plain,
% 1.35/1.57      (![X22 : $i]:
% 1.35/1.57         (((k3_relat_1 @ X22)
% 1.35/1.57            = (k2_xboole_0 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 1.35/1.57          | ~ (v1_relat_1 @ X22))),
% 1.35/1.57      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.35/1.57  thf(t7_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.35/1.57  thf('28', plain,
% 1.35/1.57      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 1.35/1.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.35/1.57  thf('29', plain,
% 1.35/1.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.35/1.57         (~ (r1_tarski @ X10 @ X11)
% 1.35/1.57          | ~ (r1_tarski @ X11 @ X12)
% 1.35/1.57          | (r1_tarski @ X10 @ X12))),
% 1.35/1.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.35/1.57  thf('30', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.35/1.57      inference('sup-', [status(thm)], ['28', '29'])).
% 1.35/1.57  thf('31', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['27', '30'])).
% 1.35/1.57  thf('32', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['26', '31'])).
% 1.35/1.57  thf('33', plain,
% 1.35/1.57      (![X27 : $i, X28 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k2_wellord1 @ X27 @ X28)))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.35/1.57  thf('34', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.35/1.57          | ~ (v1_relat_1 @ X0))),
% 1.35/1.57      inference('clc', [status(thm)], ['32', '33'])).
% 1.35/1.57  thf(t97_relat_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ B ) =>
% 1.35/1.57       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.35/1.57         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.35/1.57  thf('35', plain,
% 1.35/1.57      (![X25 : $i, X26 : $i]:
% 1.35/1.57         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 1.35/1.57          | ((k7_relat_1 @ X25 @ X26) = (X25))
% 1.35/1.57          | ~ (v1_relat_1 @ X25))),
% 1.35/1.57      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.35/1.57  thf('36', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 1.35/1.57          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.35/1.57              = (k2_wellord1 @ X0 @ sk_A)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['34', '35'])).
% 1.35/1.57  thf('37', plain,
% 1.35/1.57      (![X27 : $i, X28 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k2_wellord1 @ X27 @ X28)))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.35/1.57  thf('38', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.35/1.57            = (k2_wellord1 @ X0 @ sk_A))
% 1.35/1.57          | ~ (v1_relat_1 @ X0))),
% 1.35/1.57      inference('clc', [status(thm)], ['36', '37'])).
% 1.35/1.57  thf(t18_wellord1, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ B ) =>
% 1.35/1.57       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 1.35/1.57  thf('39', plain,
% 1.35/1.57      (![X29 : $i, X30 : $i]:
% 1.35/1.57         (((k2_wellord1 @ X30 @ X29)
% 1.35/1.57            = (k8_relat_1 @ X29 @ (k7_relat_1 @ X30 @ X29)))
% 1.35/1.57          | ~ (v1_relat_1 @ X30))),
% 1.35/1.57      inference('cnf', [status(esa)], [t18_wellord1])).
% 1.35/1.57  thf('40', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.35/1.57            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 1.35/1.57      inference('sup+', [status(thm)], ['38', '39'])).
% 1.35/1.57  thf('41', plain,
% 1.35/1.57      (![X27 : $i, X28 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k2_wellord1 @ X27 @ X28)))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.35/1.57  thf('42', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.35/1.57              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 1.35/1.57      inference('clc', [status(thm)], ['40', '41'])).
% 1.35/1.57  thf('43', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 1.35/1.57            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ X0))),
% 1.35/1.57      inference('sup+', [status(thm)], ['25', '42'])).
% 1.35/1.57  thf('44', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 1.35/1.57              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 1.35/1.57      inference('simplify', [status(thm)], ['43'])).
% 1.35/1.57  thf('45', plain,
% 1.35/1.57      (((k2_wellord1 @ (k2_wellord1 @ sk_C_1 @ sk_B) @ sk_A)
% 1.35/1.57         != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('46', plain,
% 1.35/1.57      ((((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C_1 @ sk_A))
% 1.35/1.57          != (k2_wellord1 @ sk_C_1 @ sk_A))
% 1.35/1.57        | ~ (v1_relat_1 @ sk_C_1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['44', '45'])).
% 1.35/1.57  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('48', plain,
% 1.35/1.57      (((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C_1 @ sk_A))
% 1.35/1.57         != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 1.35/1.57      inference('demod', [status(thm)], ['46', '47'])).
% 1.35/1.57  thf('49', plain,
% 1.35/1.57      ((((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))
% 1.35/1.57        | ~ (v1_relat_1 @ sk_C_1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['24', '48'])).
% 1.35/1.57  thf('50', plain, ((v1_relat_1 @ sk_C_1)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('51', plain,
% 1.35/1.57      (((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 1.35/1.57      inference('demod', [status(thm)], ['49', '50'])).
% 1.35/1.57  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 1.35/1.57  
% 1.35/1.57  % SZS output end Refutation
% 1.35/1.57  
% 1.41/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
