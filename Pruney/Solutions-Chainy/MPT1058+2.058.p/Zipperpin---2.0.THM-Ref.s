%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kohzyy3bMt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:45 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 223 expanded)
%              Number of leaves         :   25 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  709 (1810 expanded)
%              Number of equality atoms :   37 ( 124 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X20 @ ( k10_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k1_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X30 @ X29 ) @ X31 )
      | ( r1_tarski @ X29 @ ( k10_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X10 @ X11 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X24 ) )
        = ( k3_xboole_0 @ X24 @ ( k9_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t158_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( r1_tarski @ X26 @ ( k2_relat_1 @ X28 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X28 @ X26 ) @ ( k10_relat_1 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t158_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('50',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('51',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','55'])).

thf('57',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['33','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','54'])).

thf('59',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k3_xboole_0 @ X17 @ ( k10_relat_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('61',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kohzyy3bMt
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 159 iterations in 0.126s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(t175_funct_2, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.58       ( ![B:$i,C:$i]:
% 0.38/0.58         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.38/0.58           ( ( k10_relat_1 @ A @ C ) =
% 0.38/0.58             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.58          ( ![B:$i,C:$i]:
% 0.38/0.58            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.38/0.58              ( ( k10_relat_1 @ A @ C ) =
% 0.38/0.58                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.38/0.58  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t71_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.58       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.58  thf('1', plain, (![X14 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf(t169_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X12 : $i]:
% 0.38/0.58         (((k10_relat_1 @ X12 @ (k2_relat_1 @ X12)) = (k1_relat_1 @ X12))
% 0.38/0.58          | ~ (v1_relat_1 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.38/0.58            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('4', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf(fc3_funct_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.58       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.58  thf('5', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.58  thf(t145_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.58       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i]:
% 0.38/0.58         ((r1_tarski @ (k9_relat_1 @ X20 @ (k10_relat_1 @ X20 @ X21)) @ X21)
% 0.38/0.58          | ~ (v1_funct_1 @ X20)
% 0.38/0.58          | ~ (v1_relat_1 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.58          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf('9', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('10', plain, (![X16 : $i]: (v1_funct_1 @ (k6_relat_1 @ X16))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)),
% 0.38/0.58      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.58  thf(t1_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.58       ( r1_tarski @ A @ C ) ))).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X3 @ X4)
% 0.38/0.58          | ~ (r1_tarski @ X4 @ X5)
% 0.38/0.58          | (r1_tarski @ X3 @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.38/0.58          | ~ (r1_tarski @ X0 @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      ((r1_tarski @ 
% 0.38/0.58        (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.38/0.58         (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.38/0.58        sk_B)),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '13'])).
% 0.38/0.58  thf('15', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf(d10_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.58  thf(t163_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.58       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.58           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.38/0.58         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 0.38/0.58          | ~ (r1_tarski @ (k9_relat_1 @ X30 @ X29) @ X31)
% 0.38/0.58          | (r1_tarski @ X29 @ (k10_relat_1 @ X30 @ X31))
% 0.38/0.58          | ~ (v1_funct_1 @ X30)
% 0.38/0.58          | ~ (v1_relat_1 @ X30))),
% 0.38/0.58      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.38/0.58          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.38/0.58          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.38/0.58             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.58          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.38/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['15', '19'])).
% 0.38/0.58  thf('21', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf('22', plain, (![X16 : $i]: (v1_funct_1 @ (k6_relat_1 @ X16))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('23', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.38/0.58          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.38/0.58      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.38/0.58        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['14', '24'])).
% 0.38/0.58  thf('26', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf(t167_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i]:
% 0.38/0.58         ((r1_tarski @ (k10_relat_1 @ X10 @ X11) @ (k1_relat_1 @ X10))
% 0.38/0.58          | ~ (v1_relat_1 @ X10))),
% 0.38/0.58      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.58  thf('29', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.38/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X0 : $i, X2 : $i]:
% 0.38/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.58          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (((k10_relat_1 @ sk_A @ sk_C)
% 0.38/0.58         = (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['25', '32'])).
% 0.38/0.58  thf('34', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf(t148_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.58       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.38/0.58         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X24 : $i, X25 : $i]:
% 0.38/0.58         (((k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X24))
% 0.38/0.58            = (k3_xboole_0 @ X24 @ (k9_relat_1 @ X25 @ (k1_relat_1 @ X25))))
% 0.38/0.58          | ~ (v1_funct_1 @ X25)
% 0.38/0.58          | ~ (v1_relat_1 @ X25))),
% 0.38/0.58      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.38/0.58            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.58            = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.58          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf('37', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('38', plain, (![X16 : $i]: (v1_funct_1 @ (k6_relat_1 @ X16))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.38/0.58           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.58           = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)),
% 0.38/0.58      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      (![X0 : $i, X2 : $i]:
% 0.38/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.38/0.58          | ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.58  thf('43', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.38/0.58          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.38/0.58      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (r1_tarski @ X0 @ 
% 0.38/0.58          (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.38/0.58           (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.58  thf(t158_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.58       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.38/0.58           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.38/0.58         ( r1_tarski @ A @ B ) ) ))).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.58         ((r1_tarski @ X26 @ X27)
% 0.38/0.58          | ~ (v1_relat_1 @ X28)
% 0.38/0.58          | ~ (v1_funct_1 @ X28)
% 0.38/0.58          | ~ (r1_tarski @ X26 @ (k2_relat_1 @ X28))
% 0.38/0.58          | ~ (r1_tarski @ (k10_relat_1 @ X28 @ X26) @ 
% 0.38/0.58               (k10_relat_1 @ X28 @ X27)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t158_funct_1])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.58          | ~ (r1_tarski @ X0 @ (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.38/0.58          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.38/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.58          | (r1_tarski @ X0 @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.58  thf('49', plain, (![X14 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf('50', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.58  thf('51', plain, (![X16 : $i]: (v1_funct_1 @ (k6_relat_1 @ X16))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('52', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.58          | (r1_tarski @ X0 @ X1))),
% 0.38/0.58      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (![X0 : $i]: (r1_tarski @ X0 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['45', '53'])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['42', '54'])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.38/0.58           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (k3_xboole_0 @ X1 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['39', '55'])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.38/0.58         (k10_relat_1 @ sk_A @ sk_C))
% 0.38/0.58         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['33', '56'])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['42', '54'])).
% 0.38/0.58  thf('59', plain,
% 0.38/0.58      (((k10_relat_1 @ sk_A @ sk_C)
% 0.38/0.58         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.38/0.58      inference('demod', [status(thm)], ['57', '58'])).
% 0.38/0.58  thf(t139_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ C ) =>
% 0.38/0.58       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.38/0.58         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.58         (((k10_relat_1 @ (k7_relat_1 @ X18 @ X17) @ X19)
% 0.38/0.58            = (k3_xboole_0 @ X17 @ (k10_relat_1 @ X18 @ X19)))
% 0.38/0.58          | ~ (v1_relat_1 @ X18))),
% 0.38/0.58      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.38/0.58  thf('61', plain,
% 0.38/0.58      (((k10_relat_1 @ sk_A @ sk_C)
% 0.38/0.58         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.38/0.58          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.58  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      (((k10_relat_1 @ sk_A @ sk_C)
% 0.38/0.58         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.38/0.58      inference('demod', [status(thm)], ['62', '63'])).
% 0.38/0.58  thf('65', plain, ($false),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['59', '64'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
