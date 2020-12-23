%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P1qtUNMNEB

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:28 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 139 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  738 (1177 expanded)
%              Number of equality atoms :   38 (  70 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) )
        = ( k9_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X30: $i] :
      ( ( ( k10_relat_1 @ X30 @ ( k2_relat_1 @ X30 ) )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k7_relat_1 @ X49 @ X48 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X48 ) @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('7',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X43 ) @ X42 ) @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X31 @ X33 ) )
      | ~ ( r1_tarski @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k10_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k7_relat_1 @ X49 @ X48 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X48 ) @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('19',plain,(
    ! [X41: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('20',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X44 ) @ X45 )
      | ( ( k5_relat_1 @ X44 @ ( k6_relat_1 @ X45 ) )
        = X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k7_relat_1 @ X35 @ ( k1_relat_1 @ X34 ) )
        = ( k7_relat_1 @ X35 @ ( k1_relat_1 @ ( k7_relat_1 @ X34 @ ( k1_relat_1 @ X35 ) ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('35',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k7_relat_1 @ X49 @ X48 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X48 ) @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('37',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('38',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) ) @ X47 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('39',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('41',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('44',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35','47','48'])).

thf('50',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( ( k7_relat_1 @ X35 @ ( k1_relat_1 @ X34 ) )
        = ( k7_relat_1 @ X35 @ ( k1_relat_1 @ ( k7_relat_1 @ X34 @ ( k1_relat_1 @ X35 ) ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('51',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) ) @ X47 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('56',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X50: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('60',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P1qtUNMNEB
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.22/2.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.22/2.44  % Solved by: fo/fo7.sh
% 2.22/2.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.22/2.44  % done 2425 iterations in 1.985s
% 2.22/2.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.22/2.44  % SZS output start Refutation
% 2.22/2.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.22/2.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.22/2.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.22/2.44  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.22/2.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.22/2.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.22/2.44  thf(sk_A_type, type, sk_A: $i).
% 2.22/2.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.22/2.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.22/2.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.22/2.44  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.22/2.44  thf(sk_B_type, type, sk_B: $i).
% 2.22/2.44  thf(t146_funct_1, conjecture,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ B ) =>
% 2.22/2.44       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.22/2.44         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 2.22/2.44  thf(zf_stmt_0, negated_conjecture,
% 2.22/2.44    (~( ![A:$i,B:$i]:
% 2.22/2.44        ( ( v1_relat_1 @ B ) =>
% 2.22/2.44          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.22/2.44            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 2.22/2.44    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 2.22/2.44  thf('0', plain,
% 2.22/2.44      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf(t148_relat_1, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ B ) =>
% 2.22/2.44       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.22/2.44  thf('1', plain,
% 2.22/2.44      (![X28 : $i, X29 : $i]:
% 2.22/2.44         (((k2_relat_1 @ (k7_relat_1 @ X28 @ X29)) = (k9_relat_1 @ X28 @ X29))
% 2.22/2.44          | ~ (v1_relat_1 @ X28))),
% 2.22/2.44      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.22/2.44  thf(t169_relat_1, axiom,
% 2.22/2.44    (![A:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ A ) =>
% 2.22/2.44       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.22/2.44  thf('2', plain,
% 2.22/2.44      (![X30 : $i]:
% 2.22/2.44         (((k10_relat_1 @ X30 @ (k2_relat_1 @ X30)) = (k1_relat_1 @ X30))
% 2.22/2.44          | ~ (v1_relat_1 @ X30))),
% 2.22/2.44      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.22/2.44  thf('3', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.22/2.44            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.22/2.44          | ~ (v1_relat_1 @ X1)
% 2.22/2.44          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.22/2.44      inference('sup+', [status(thm)], ['1', '2'])).
% 2.22/2.44  thf(dt_k7_relat_1, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.22/2.44  thf('4', plain,
% 2.22/2.44      (![X26 : $i, X27 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k7_relat_1 @ X26 @ X27)))),
% 2.22/2.44      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.22/2.44  thf('5', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X1)
% 2.22/2.44          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 2.22/2.44              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.22/2.44      inference('clc', [status(thm)], ['3', '4'])).
% 2.22/2.44  thf(t94_relat_1, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ B ) =>
% 2.22/2.44       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.22/2.44  thf('6', plain,
% 2.22/2.44      (![X48 : $i, X49 : $i]:
% 2.22/2.44         (((k7_relat_1 @ X49 @ X48) = (k5_relat_1 @ (k6_relat_1 @ X48) @ X49))
% 2.22/2.44          | ~ (v1_relat_1 @ X49))),
% 2.22/2.44      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.22/2.44  thf(t76_relat_1, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ B ) =>
% 2.22/2.44       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 2.22/2.44         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 2.22/2.44  thf('7', plain,
% 2.22/2.44      (![X42 : $i, X43 : $i]:
% 2.22/2.44         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X43) @ X42) @ X42)
% 2.22/2.44          | ~ (v1_relat_1 @ X42))),
% 2.22/2.44      inference('cnf', [status(esa)], [t76_relat_1])).
% 2.22/2.44  thf('8', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X1)
% 2.22/2.44          | ~ (v1_relat_1 @ X1)
% 2.22/2.44          | ~ (v1_relat_1 @ X1))),
% 2.22/2.44      inference('sup+', [status(thm)], ['6', '7'])).
% 2.22/2.44  thf('9', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X1) | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X1))),
% 2.22/2.44      inference('simplify', [status(thm)], ['8'])).
% 2.22/2.44  thf(t179_relat_1, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ B ) =>
% 2.22/2.44       ( ![C:$i]:
% 2.22/2.44         ( ( v1_relat_1 @ C ) =>
% 2.22/2.44           ( ( r1_tarski @ B @ C ) =>
% 2.22/2.44             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 2.22/2.44  thf('10', plain,
% 2.22/2.44      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X31)
% 2.22/2.44          | (r1_tarski @ (k10_relat_1 @ X32 @ X33) @ (k10_relat_1 @ X31 @ X33))
% 2.22/2.44          | ~ (r1_tarski @ X32 @ X31)
% 2.22/2.44          | ~ (v1_relat_1 @ X32))),
% 2.22/2.44      inference('cnf', [status(esa)], [t179_relat_1])).
% 2.22/2.44  thf('11', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X0)
% 2.22/2.44          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 2.22/2.44          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 2.22/2.44             (k10_relat_1 @ X0 @ X2))
% 2.22/2.44          | ~ (v1_relat_1 @ X0))),
% 2.22/2.44      inference('sup-', [status(thm)], ['9', '10'])).
% 2.22/2.44  thf('12', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.44         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 2.22/2.44           (k10_relat_1 @ X0 @ X2))
% 2.22/2.44          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 2.22/2.44          | ~ (v1_relat_1 @ X0))),
% 2.22/2.44      inference('simplify', [status(thm)], ['11'])).
% 2.22/2.44  thf('13', plain,
% 2.22/2.44      (![X26 : $i, X27 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k7_relat_1 @ X26 @ X27)))),
% 2.22/2.44      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.22/2.44  thf('14', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X0)
% 2.22/2.44          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 2.22/2.44             (k10_relat_1 @ X0 @ X2)))),
% 2.22/2.44      inference('clc', [status(thm)], ['12', '13'])).
% 2.22/2.44  thf('15', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.22/2.44           (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 2.22/2.44          | ~ (v1_relat_1 @ X1)
% 2.22/2.44          | ~ (v1_relat_1 @ X1))),
% 2.22/2.44      inference('sup+', [status(thm)], ['5', '14'])).
% 2.22/2.44  thf('16', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X1)
% 2.22/2.44          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.22/2.44             (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 2.22/2.44      inference('simplify', [status(thm)], ['15'])).
% 2.22/2.44  thf('17', plain,
% 2.22/2.44      (![X48 : $i, X49 : $i]:
% 2.22/2.44         (((k7_relat_1 @ X49 @ X48) = (k5_relat_1 @ (k6_relat_1 @ X48) @ X49))
% 2.22/2.44          | ~ (v1_relat_1 @ X49))),
% 2.22/2.44      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.22/2.44  thf('18', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf(t71_relat_1, axiom,
% 2.22/2.44    (![A:$i]:
% 2.22/2.44     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.22/2.44       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.22/2.44  thf('19', plain, (![X41 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 2.22/2.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.22/2.44  thf(t79_relat_1, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ B ) =>
% 2.22/2.44       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.22/2.44         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.22/2.44  thf('20', plain,
% 2.22/2.44      (![X44 : $i, X45 : $i]:
% 2.22/2.44         (~ (r1_tarski @ (k2_relat_1 @ X44) @ X45)
% 2.22/2.44          | ((k5_relat_1 @ X44 @ (k6_relat_1 @ X45)) = (X44))
% 2.22/2.44          | ~ (v1_relat_1 @ X44))),
% 2.22/2.44      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.22/2.44  thf('21', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (r1_tarski @ X0 @ X1)
% 2.22/2.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.22/2.44          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.22/2.44              = (k6_relat_1 @ X0)))),
% 2.22/2.44      inference('sup-', [status(thm)], ['19', '20'])).
% 2.22/2.44  thf(fc3_funct_1, axiom,
% 2.22/2.44    (![A:$i]:
% 2.22/2.44     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.22/2.44       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.22/2.44  thf('22', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 2.22/2.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.22/2.44  thf('23', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (r1_tarski @ X0 @ X1)
% 2.22/2.44          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.22/2.44              = (k6_relat_1 @ X0)))),
% 2.22/2.44      inference('demod', [status(thm)], ['21', '22'])).
% 2.22/2.44  thf('24', plain,
% 2.22/2.44      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 2.22/2.44         = (k6_relat_1 @ sk_A))),
% 2.22/2.44      inference('sup-', [status(thm)], ['18', '23'])).
% 2.22/2.44  thf('25', plain,
% 2.22/2.44      ((((k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)
% 2.22/2.44          = (k6_relat_1 @ sk_A))
% 2.22/2.44        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 2.22/2.44      inference('sup+', [status(thm)], ['17', '24'])).
% 2.22/2.44  thf('26', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 2.22/2.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.22/2.44  thf('27', plain,
% 2.22/2.44      (((k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)
% 2.22/2.44         = (k6_relat_1 @ sk_A))),
% 2.22/2.44      inference('demod', [status(thm)], ['25', '26'])).
% 2.22/2.44  thf('28', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 2.22/2.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.22/2.44  thf(t189_relat_1, axiom,
% 2.22/2.44    (![A:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ A ) =>
% 2.22/2.44       ( ![B:$i]:
% 2.22/2.44         ( ( v1_relat_1 @ B ) =>
% 2.22/2.44           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 2.22/2.44             ( k7_relat_1 @
% 2.22/2.44               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 2.22/2.44  thf('29', plain,
% 2.22/2.44      (![X34 : $i, X35 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X34)
% 2.22/2.44          | ((k7_relat_1 @ X35 @ (k1_relat_1 @ X34))
% 2.22/2.44              = (k7_relat_1 @ X35 @ 
% 2.22/2.44                 (k1_relat_1 @ (k7_relat_1 @ X34 @ (k1_relat_1 @ X35)))))
% 2.22/2.44          | ~ (v1_relat_1 @ X35))),
% 2.22/2.44      inference('cnf', [status(esa)], [t189_relat_1])).
% 2.22/2.44  thf('30', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (((k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 2.22/2.44            = (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.22/2.44               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.22/2.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.22/2.44          | ~ (v1_relat_1 @ X1))),
% 2.22/2.44      inference('sup+', [status(thm)], ['28', '29'])).
% 2.22/2.44  thf('31', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 2.22/2.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.22/2.44  thf('32', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (((k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 2.22/2.44            = (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.22/2.44               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.22/2.44          | ~ (v1_relat_1 @ X1))),
% 2.22/2.44      inference('demod', [status(thm)], ['30', '31'])).
% 2.22/2.44  thf('33', plain,
% 2.22/2.44      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 2.22/2.44          (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))
% 2.22/2.44          = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 2.22/2.44             (k1_relat_1 @ (k6_relat_1 @ sk_A))))
% 2.22/2.44        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 2.22/2.44      inference('sup+', [status(thm)], ['27', '32'])).
% 2.22/2.44  thf('34', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 2.22/2.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.22/2.44  thf('35', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 2.22/2.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.22/2.44  thf('36', plain,
% 2.22/2.44      (![X48 : $i, X49 : $i]:
% 2.22/2.44         (((k7_relat_1 @ X49 @ X48) = (k5_relat_1 @ (k6_relat_1 @ X48) @ X49))
% 2.22/2.44          | ~ (v1_relat_1 @ X49))),
% 2.22/2.44      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.22/2.44  thf('37', plain,
% 2.22/2.44      (((k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A)
% 2.22/2.44         = (k6_relat_1 @ sk_A))),
% 2.22/2.44      inference('demod', [status(thm)], ['25', '26'])).
% 2.22/2.44  thf(t87_relat_1, axiom,
% 2.22/2.44    (![A:$i,B:$i]:
% 2.22/2.44     ( ( v1_relat_1 @ B ) =>
% 2.22/2.44       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 2.22/2.44  thf('38', plain,
% 2.22/2.44      (![X46 : $i, X47 : $i]:
% 2.22/2.44         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X46 @ X47)) @ X47)
% 2.22/2.44          | ~ (v1_relat_1 @ X46))),
% 2.22/2.44      inference('cnf', [status(esa)], [t87_relat_1])).
% 2.22/2.44  thf('39', plain,
% 2.22/2.44      (((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ sk_A)
% 2.22/2.44        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 2.22/2.44      inference('sup+', [status(thm)], ['37', '38'])).
% 2.22/2.44  thf('40', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 2.22/2.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.22/2.44  thf('41', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 2.22/2.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.22/2.44  thf('42', plain, ((r1_tarski @ sk_A @ sk_A)),
% 2.22/2.44      inference('demod', [status(thm)], ['39', '40', '41'])).
% 2.22/2.44  thf('43', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (r1_tarski @ X0 @ X1)
% 2.22/2.44          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.22/2.44              = (k6_relat_1 @ X0)))),
% 2.22/2.44      inference('demod', [status(thm)], ['21', '22'])).
% 2.22/2.44  thf('44', plain,
% 2.22/2.44      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_A))
% 2.22/2.44         = (k6_relat_1 @ sk_A))),
% 2.22/2.44      inference('sup-', [status(thm)], ['42', '43'])).
% 2.22/2.44  thf('45', plain,
% 2.22/2.44      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_A) = (k6_relat_1 @ sk_A))
% 2.22/2.44        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.22/2.44      inference('sup+', [status(thm)], ['36', '44'])).
% 2.22/2.44  thf('46', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 2.22/2.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.22/2.44  thf('47', plain,
% 2.22/2.44      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_A) = (k6_relat_1 @ sk_A))),
% 2.22/2.44      inference('demod', [status(thm)], ['45', '46'])).
% 2.22/2.44  thf('48', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 2.22/2.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.22/2.44  thf('49', plain,
% 2.22/2.44      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 2.22/2.44         = (k6_relat_1 @ sk_A))),
% 2.22/2.44      inference('demod', [status(thm)], ['33', '34', '35', '47', '48'])).
% 2.22/2.44  thf('50', plain,
% 2.22/2.44      (![X34 : $i, X35 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X34)
% 2.22/2.44          | ((k7_relat_1 @ X35 @ (k1_relat_1 @ X34))
% 2.22/2.44              = (k7_relat_1 @ X35 @ 
% 2.22/2.44                 (k1_relat_1 @ (k7_relat_1 @ X34 @ (k1_relat_1 @ X35)))))
% 2.22/2.44          | ~ (v1_relat_1 @ X35))),
% 2.22/2.44      inference('cnf', [status(esa)], [t189_relat_1])).
% 2.22/2.44  thf('51', plain,
% 2.22/2.44      (![X46 : $i, X47 : $i]:
% 2.22/2.44         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X46 @ X47)) @ X47)
% 2.22/2.44          | ~ (v1_relat_1 @ X46))),
% 2.22/2.44      inference('cnf', [status(esa)], [t87_relat_1])).
% 2.22/2.44  thf('52', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 2.22/2.44           (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))))
% 2.22/2.44          | ~ (v1_relat_1 @ X1)
% 2.22/2.44          | ~ (v1_relat_1 @ X0)
% 2.22/2.44          | ~ (v1_relat_1 @ X1))),
% 2.22/2.44      inference('sup+', [status(thm)], ['50', '51'])).
% 2.22/2.44  thf('53', plain,
% 2.22/2.44      (![X0 : $i, X1 : $i]:
% 2.22/2.44         (~ (v1_relat_1 @ X0)
% 2.22/2.44          | ~ (v1_relat_1 @ X1)
% 2.22/2.44          | (r1_tarski @ 
% 2.22/2.44             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 2.22/2.44             (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))))),
% 2.22/2.44      inference('simplify', [status(thm)], ['52'])).
% 2.22/2.44  thf('54', plain,
% 2.22/2.44      (((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ 
% 2.22/2.44         (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A)))))
% 2.22/2.44        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 2.22/2.44        | ~ (v1_relat_1 @ sk_B))),
% 2.22/2.44      inference('sup+', [status(thm)], ['49', '53'])).
% 2.22/2.44  thf('55', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 2.22/2.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.22/2.44  thf('56', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 2.22/2.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.22/2.44  thf('57', plain, (![X50 : $i]: (v1_relat_1 @ (k6_relat_1 @ X50))),
% 2.22/2.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.22/2.44  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('59', plain,
% 2.22/2.44      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 2.22/2.44      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 2.22/2.44  thf(t1_xboole_1, axiom,
% 2.22/2.44    (![A:$i,B:$i,C:$i]:
% 2.22/2.44     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.22/2.44       ( r1_tarski @ A @ C ) ))).
% 2.22/2.44  thf('60', plain,
% 2.22/2.44      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.22/2.44         (~ (r1_tarski @ X2 @ X3)
% 2.22/2.44          | ~ (r1_tarski @ X3 @ X4)
% 2.22/2.44          | (r1_tarski @ X2 @ X4))),
% 2.22/2.44      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.22/2.44  thf('61', plain,
% 2.22/2.44      (![X0 : $i]:
% 2.22/2.44         ((r1_tarski @ sk_A @ X0)
% 2.22/2.44          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ X0))),
% 2.22/2.44      inference('sup-', [status(thm)], ['59', '60'])).
% 2.22/2.44  thf('62', plain,
% 2.22/2.44      ((~ (v1_relat_1 @ sk_B)
% 2.22/2.44        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 2.22/2.44      inference('sup-', [status(thm)], ['16', '61'])).
% 2.22/2.44  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 2.22/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.44  thf('64', plain,
% 2.22/2.44      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 2.22/2.44      inference('demod', [status(thm)], ['62', '63'])).
% 2.22/2.44  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 2.22/2.44  
% 2.22/2.44  % SZS output end Refutation
% 2.22/2.44  
% 2.22/2.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
