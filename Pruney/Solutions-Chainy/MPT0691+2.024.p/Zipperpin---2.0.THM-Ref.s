%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dtK8oASczO

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:20 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 147 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :  651 (1257 expanded)
%              Number of equality atoms :   37 (  52 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X25: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X23 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','23','24'])).

thf('26',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('31',plain,(
    ! [X25: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('32',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','40','41','42'])).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X23 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['29','59'])).

thf('61',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dtK8oASczO
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.41/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.63  % Solved by: fo/fo7.sh
% 0.41/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.63  % done 361 iterations in 0.178s
% 0.41/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.63  % SZS output start Refutation
% 0.41/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.63  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.63  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.41/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.63  thf(t146_funct_1, conjecture,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ B ) =>
% 0.41/0.63       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.63         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.41/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.63    (~( ![A:$i,B:$i]:
% 0.41/0.63        ( ( v1_relat_1 @ B ) =>
% 0.41/0.63          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.63            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.41/0.63    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.41/0.63  thf('0', plain,
% 0.41/0.63      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(t139_funct_1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ C ) =>
% 0.41/0.63       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.41/0.63         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.41/0.63  thf('1', plain,
% 0.41/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.63         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 0.41/0.63            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 0.41/0.63          | ~ (v1_relat_1 @ X31))),
% 0.41/0.63      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.41/0.63  thf(t148_relat_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ B ) =>
% 0.41/0.63       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.41/0.63  thf('2', plain,
% 0.41/0.63      (![X21 : $i, X22 : $i]:
% 0.41/0.63         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 0.41/0.63          | ~ (v1_relat_1 @ X21))),
% 0.41/0.63      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.63  thf(t169_relat_1, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ A ) =>
% 0.41/0.63       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.41/0.63  thf('3', plain,
% 0.41/0.63      (![X25 : $i]:
% 0.41/0.63         (((k10_relat_1 @ X25 @ (k2_relat_1 @ X25)) = (k1_relat_1 @ X25))
% 0.41/0.63          | ~ (v1_relat_1 @ X25))),
% 0.41/0.63      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.41/0.63  thf('4', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.41/0.63            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.41/0.63          | ~ (v1_relat_1 @ X1)
% 0.41/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['2', '3'])).
% 0.41/0.63  thf(dt_k7_relat_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.41/0.63  thf('5', plain,
% 0.41/0.63      (![X19 : $i, X20 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k7_relat_1 @ X19 @ X20)))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.63  thf('6', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X1)
% 0.41/0.63          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.41/0.63              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.41/0.63      inference('clc', [status(thm)], ['4', '5'])).
% 0.41/0.63  thf('7', plain,
% 0.41/0.63      (![X19 : $i, X20 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k7_relat_1 @ X19 @ X20)))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.63  thf('8', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(t91_relat_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ B ) =>
% 0.41/0.63       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.63         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.41/0.63  thf('9', plain,
% 0.41/0.63      (![X28 : $i, X29 : $i]:
% 0.41/0.63         (~ (r1_tarski @ X28 @ (k1_relat_1 @ X29))
% 0.41/0.63          | ((k1_relat_1 @ (k7_relat_1 @ X29 @ X28)) = (X28))
% 0.41/0.63          | ~ (v1_relat_1 @ X29))),
% 0.41/0.63      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.41/0.63  thf('10', plain,
% 0.41/0.63      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.63        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.63  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('12', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.41/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.41/0.63  thf(t167_relat_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ B ) =>
% 0.41/0.63       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.41/0.63  thf('13', plain,
% 0.41/0.63      (![X23 : $i, X24 : $i]:
% 0.41/0.63         ((r1_tarski @ (k10_relat_1 @ X23 @ X24) @ (k1_relat_1 @ X23))
% 0.41/0.63          | ~ (v1_relat_1 @ X23))),
% 0.41/0.63      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.41/0.63  thf('14', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.41/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['12', '13'])).
% 0.41/0.63  thf('15', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ sk_B)
% 0.41/0.63          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['7', '14'])).
% 0.41/0.63  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('17', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 0.41/0.63      inference('demod', [status(thm)], ['15', '16'])).
% 0.41/0.63  thf(d10_xboole_0, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.63  thf('18', plain,
% 0.41/0.63      (![X6 : $i, X8 : $i]:
% 0.41/0.63         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.41/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.63  thf('19', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 0.41/0.63          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.63  thf('20', plain,
% 0.41/0.63      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.41/0.63        | ~ (v1_relat_1 @ sk_B)
% 0.41/0.63        | ((sk_A)
% 0.41/0.63            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.41/0.63               (k9_relat_1 @ sk_B @ sk_A))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['6', '19'])).
% 0.41/0.63  thf('21', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.41/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.41/0.63  thf('22', plain,
% 0.41/0.63      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.41/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.63  thf('23', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.41/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.41/0.63  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('25', plain,
% 0.41/0.63      (((sk_A)
% 0.41/0.63         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.41/0.63            (k9_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.63      inference('demod', [status(thm)], ['20', '21', '23', '24'])).
% 0.41/0.63  thf('26', plain,
% 0.41/0.63      ((((sk_A)
% 0.41/0.63          = (k3_xboole_0 @ sk_A @ 
% 0.41/0.63             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.41/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.63      inference('sup+', [status(thm)], ['1', '25'])).
% 0.41/0.63  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('28', plain,
% 0.41/0.63      (((sk_A)
% 0.41/0.63         = (k3_xboole_0 @ sk_A @ 
% 0.41/0.63            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.41/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.41/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.63  thf('29', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.63  thf('30', plain,
% 0.41/0.63      (![X19 : $i, X20 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k7_relat_1 @ X19 @ X20)))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.63  thf('31', plain,
% 0.41/0.63      (![X25 : $i]:
% 0.41/0.63         (((k10_relat_1 @ X25 @ (k2_relat_1 @ X25)) = (k1_relat_1 @ X25))
% 0.41/0.63          | ~ (v1_relat_1 @ X25))),
% 0.41/0.63      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.41/0.63  thf('32', plain,
% 0.41/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.63         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 0.41/0.63            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 0.41/0.63          | ~ (v1_relat_1 @ X31))),
% 0.41/0.63      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.41/0.63  thf('33', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 0.41/0.63          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.63  thf('34', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (r1_tarski @ sk_A @ 
% 0.41/0.63             (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 0.41/0.63          | ~ (v1_relat_1 @ sk_B)
% 0.41/0.63          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.63  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('36', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (r1_tarski @ sk_A @ 
% 0.41/0.63             (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 0.41/0.63          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 0.41/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.41/0.63  thf('37', plain,
% 0.41/0.63      ((~ (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.41/0.63        | ~ (v1_relat_1 @ sk_B)
% 0.41/0.63        | ((sk_A)
% 0.41/0.63            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['31', '36'])).
% 0.41/0.63  thf('38', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(t28_xboole_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.63  thf('39', plain,
% 0.41/0.63      (![X14 : $i, X15 : $i]:
% 0.41/0.63         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.41/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.63  thf('40', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.63  thf('41', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.41/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.41/0.63  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('43', plain,
% 0.41/0.63      (((sk_A)
% 0.41/0.63         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.41/0.63      inference('demod', [status(thm)], ['37', '40', '41', '42'])).
% 0.41/0.63  thf('44', plain,
% 0.41/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.63         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 0.41/0.63            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 0.41/0.63          | ~ (v1_relat_1 @ X31))),
% 0.41/0.63      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.41/0.63  thf(t87_relat_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ B ) =>
% 0.41/0.63       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.41/0.63  thf('45', plain,
% 0.41/0.63      (![X26 : $i, X27 : $i]:
% 0.41/0.63         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X26 @ X27)) @ X27)
% 0.41/0.63          | ~ (v1_relat_1 @ X26))),
% 0.41/0.63      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.41/0.63  thf('46', plain,
% 0.41/0.63      (![X23 : $i, X24 : $i]:
% 0.41/0.63         ((r1_tarski @ (k10_relat_1 @ X23 @ X24) @ (k1_relat_1 @ X23))
% 0.41/0.63          | ~ (v1_relat_1 @ X23))),
% 0.41/0.63      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.41/0.63  thf(t12_xboole_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.41/0.63  thf('47', plain,
% 0.41/0.63      (![X12 : $i, X13 : $i]:
% 0.41/0.63         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.41/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.41/0.63  thf('48', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X0)
% 0.41/0.63          | ((k2_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.41/0.63              = (k1_relat_1 @ X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.63  thf(t11_xboole_1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.41/0.63  thf('49', plain,
% 0.41/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.63         ((r1_tarski @ X9 @ X10)
% 0.41/0.63          | ~ (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 0.41/0.63      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.41/0.63  thf('50', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.41/0.63          | ~ (v1_relat_1 @ X0)
% 0.41/0.63          | (r1_tarski @ (k10_relat_1 @ X0 @ X2) @ X1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.63  thf('51', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X1)
% 0.41/0.63          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X0)
% 0.41/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['45', '50'])).
% 0.41/0.63  thf('52', plain,
% 0.41/0.63      (![X19 : $i, X20 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X19) | (v1_relat_1 @ (k7_relat_1 @ X19 @ X20)))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.63  thf('53', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X0)
% 0.41/0.63          | ~ (v1_relat_1 @ X1))),
% 0.41/0.63      inference('clc', [status(thm)], ['51', '52'])).
% 0.41/0.63  thf('54', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X2)
% 0.41/0.63          | ~ (v1_relat_1 @ X1)
% 0.41/0.63          | ~ (v1_relat_1 @ X1))),
% 0.41/0.63      inference('sup+', [status(thm)], ['44', '53'])).
% 0.41/0.63  thf('55', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X1)
% 0.41/0.63          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X2))),
% 0.41/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.41/0.63  thf('56', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ X0)
% 0.41/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['43', '55'])).
% 0.41/0.63  thf('57', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ sk_B) | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['30', '56'])).
% 0.41/0.63  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('59', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ X0)),
% 0.41/0.63      inference('demod', [status(thm)], ['57', '58'])).
% 0.41/0.63  thf('60', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0)),
% 0.41/0.63      inference('sup+', [status(thm)], ['29', '59'])).
% 0.41/0.63  thf('61', plain,
% 0.41/0.63      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['28', '60'])).
% 0.41/0.63  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.41/0.63  
% 0.41/0.63  % SZS output end Refutation
% 0.41/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
