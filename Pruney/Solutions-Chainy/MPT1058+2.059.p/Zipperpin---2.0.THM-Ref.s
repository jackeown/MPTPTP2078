%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Aq3GZSUMCE

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 185 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  692 (1560 expanded)
%              Number of equality atoms :   43 ( 122 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X19 ) ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
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
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k1_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X25 @ X24 ) @ X26 )
      | ( r1_tarski @ X24 @ ( k10_relat_1 @ X25 @ X26 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
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
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X8 @ X9 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
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
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k9_relat_1 @ X23 @ ( k10_relat_1 @ X23 @ X22 ) )
        = ( k3_xboole_0 @ X22 @ ( k9_relat_1 @ X23 @ ( k1_relat_1 @ X23 ) ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k2_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ X21 @ ( k10_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('50',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['44','45','48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','52'])).

thf('54',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['33','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['44','45','48','49','50','51'])).

thf('56',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k3_xboole_0 @ X15 @ ( k10_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('58',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Aq3GZSUMCE
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 140 iterations in 0.100s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.55  thf(t175_funct_2, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.55       ( ![B:$i,C:$i]:
% 0.37/0.55         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.37/0.55           ( ( k10_relat_1 @ A @ C ) =
% 0.37/0.55             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.55          ( ![B:$i,C:$i]:
% 0.37/0.55            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.37/0.55              ( ( k10_relat_1 @ A @ C ) =
% 0.37/0.55                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.37/0.55  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t71_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.37/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.37/0.55  thf('1', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.37/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.55  thf(t169_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X10 : $i]:
% 0.37/0.55         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 0.37/0.55          | ~ (v1_relat_1 @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.37/0.55            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.37/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('4', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.55  thf(fc3_funct_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.37/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.37/0.55  thf('5', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.37/0.55  thf(t145_funct_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i]:
% 0.37/0.56         ((r1_tarski @ (k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X19)) @ X19)
% 0.37/0.56          | ~ (v1_funct_1 @ X18)
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('9', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('10', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)),
% 0.37/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.37/0.56  thf(t1_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.56       ( r1_tarski @ A @ C ) ))).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.37/0.56          | ~ (r1_tarski @ X4 @ X5)
% 0.37/0.56          | (r1_tarski @ X3 @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.37/0.56          | ~ (r1_tarski @ X0 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      ((r1_tarski @ 
% 0.37/0.56        (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.37/0.56         (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.37/0.56        sk_B)),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '13'])).
% 0.37/0.56  thf('15', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.56  thf(d10_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.56  thf(t163_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.37/0.56           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.37/0.56         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X24 @ (k1_relat_1 @ X25))
% 0.37/0.56          | ~ (r1_tarski @ (k9_relat_1 @ X25 @ X24) @ X26)
% 0.37/0.56          | (r1_tarski @ X24 @ (k10_relat_1 @ X25 @ X26))
% 0.37/0.56          | ~ (v1_funct_1 @ X25)
% 0.37/0.56          | ~ (v1_relat_1 @ X25))),
% 0.37/0.56      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.37/0.56          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.37/0.56          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.37/0.56             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.37/0.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['15', '19'])).
% 0.37/0.56  thf('21', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.56  thf('22', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('23', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.37/0.56          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.37/0.56        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '24'])).
% 0.37/0.56  thf('26', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.56  thf(t167_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i]:
% 0.37/0.56         ((r1_tarski @ (k10_relat_1 @ X8 @ X9) @ (k1_relat_1 @ X8))
% 0.37/0.56          | ~ (v1_relat_1 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.37/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.56  thf('29', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.37/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i, X2 : $i]:
% 0.37/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.37/0.56          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_A @ sk_C)
% 0.37/0.56         = (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '32'])).
% 0.37/0.56  thf('34', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.56  thf(t148_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.37/0.56         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X22 : $i, X23 : $i]:
% 0.37/0.56         (((k9_relat_1 @ X23 @ (k10_relat_1 @ X23 @ X22))
% 0.37/0.56            = (k3_xboole_0 @ X22 @ (k9_relat_1 @ X23 @ (k1_relat_1 @ X23))))
% 0.37/0.56          | ~ (v1_funct_1 @ X23)
% 0.37/0.56          | ~ (v1_relat_1 @ X23))),
% 0.37/0.56      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.37/0.56            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.37/0.56            = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))
% 0.37/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.56  thf('37', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('38', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.37/0.56           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.37/0.56           = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.37/0.56           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.37/0.56           = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.56  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.56  thf(t147_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.37/0.56         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X20 @ (k2_relat_1 @ X21))
% 0.37/0.56          | ((k9_relat_1 @ X21 @ (k10_relat_1 @ X21 @ X20)) = (X20))
% 0.37/0.56          | ~ (v1_funct_1 @ X21)
% 0.37/0.56          | ~ (v1_relat_1 @ X21))),
% 0.37/0.56      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ X0)
% 0.37/0.56          | ~ (v1_funct_1 @ X0)
% 0.37/0.56          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.37/0.56              = (k2_relat_1 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.37/0.56            (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.37/0.56            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.37/0.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.37/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['40', '43'])).
% 0.37/0.56  thf('45', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.37/0.56           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.37/0.56           = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.37/0.56           = (k3_xboole_0 @ X0 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['46', '47'])).
% 0.37/0.56  thf('49', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.56  thf('50', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('51', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['44', '45', '48', '49', '50', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.37/0.56           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (k3_xboole_0 @ X1 @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['39', '52'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.37/0.56         (k10_relat_1 @ sk_A @ sk_C))
% 0.37/0.56         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['33', '53'])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['44', '45', '48', '49', '50', '51'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_A @ sk_C)
% 0.37/0.56         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf(t139_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ C ) =>
% 0.37/0.56       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.37/0.56         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.56         (((k10_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X17)
% 0.37/0.56            = (k3_xboole_0 @ X15 @ (k10_relat_1 @ X16 @ X17)))
% 0.37/0.56          | ~ (v1_relat_1 @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_A @ sk_C)
% 0.37/0.56         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.37/0.56          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.56  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_A @ sk_C)
% 0.37/0.56         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.37/0.56  thf('62', plain, ($false),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['56', '61'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
