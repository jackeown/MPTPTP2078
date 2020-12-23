%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7llWEG2qmh

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 167 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  628 (1468 expanded)
%              Number of equality atoms :   51 ( 112 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t154_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( ( k9_relat_1 @ B @ A )
            = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_funct_1])).

thf('0',plain,(
    ( k9_relat_1 @ sk_B @ sk_A )
 != ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ( k9_relat_1 @ sk_B @ sk_A )
 != ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','6'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k9_relat_1 @ X6 @ X7 )
        = ( k9_relat_1 @ X6 @ ( k3_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k10_relat_1 @ X11 @ ( k10_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('16',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( ( k2_relat_1 @ X15 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X8 @ X9 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k2_relat_1 @ X23 ) )
      | ( ( k9_relat_1 @ X23 @ ( k10_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) ) @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['15','32'])).

thf('34',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ X26 @ ( k2_funct_1 @ X26 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('36',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ ( k6_relat_1 @ X24 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('42',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('49',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','40','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ X0 )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ( k9_relat_1 @ sk_B @ sk_A )
 != ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7llWEG2qmh
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:53:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 133 iterations in 0.081s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.22/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.55  thf(t154_funct_1, conjecture,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.55       ( ( v2_funct_1 @ B ) =>
% 0.22/0.55         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i]:
% 0.22/0.55        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.55          ( ( v2_funct_1 @ B ) =>
% 0.22/0.55            ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t154_funct_1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      (((k9_relat_1 @ sk_B @ sk_A)
% 0.22/0.55         != (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d9_funct_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X18 : $i]:
% 0.22/0.55         (~ (v2_funct_1 @ X18)
% 0.22/0.55          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 0.22/0.55          | ~ (v1_funct_1 @ X18)
% 0.22/0.55          | ~ (v1_relat_1 @ X18))),
% 0.22/0.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      ((~ (v1_funct_1 @ sk_B)
% 0.22/0.55        | ((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))
% 0.22/0.55        | ~ (v2_funct_1 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.55  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('5', plain, ((v2_funct_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('6', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (((k9_relat_1 @ sk_B @ sk_A)
% 0.22/0.55         != (k10_relat_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['0', '6'])).
% 0.22/0.55  thf(commutativity_k2_tarski, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.22/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.55  thf(t12_setfam_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]:
% 0.22/0.55         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]:
% 0.22/0.55         ((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k3_xboole_0 @ X4 @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf(t145_relat_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ B ) =>
% 0.22/0.55       ( ( k9_relat_1 @ B @ A ) =
% 0.22/0.55         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i]:
% 0.22/0.55         (((k9_relat_1 @ X6 @ X7)
% 0.22/0.55            = (k9_relat_1 @ X6 @ (k3_xboole_0 @ (k1_relat_1 @ X6) @ X7)))
% 0.22/0.55          | ~ (v1_relat_1 @ X6))),
% 0.22/0.55      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((k9_relat_1 @ X0 @ X1)
% 0.22/0.55            = (k9_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.22/0.55          | ~ (v1_relat_1 @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf(t181_relat_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ B ) =>
% 0.22/0.55       ( ![C:$i]:
% 0.22/0.55         ( ( v1_relat_1 @ C ) =>
% 0.22/0.55           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.22/0.55             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X10)
% 0.22/0.55          | ((k10_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 0.22/0.55              = (k10_relat_1 @ X11 @ (k10_relat_1 @ X10 @ X12)))
% 0.22/0.55          | ~ (v1_relat_1 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.22/0.55  thf('16', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.55  thf(dt_k2_funct_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.22/0.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X19 : $i]:
% 0.22/0.55         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 0.22/0.55          | ~ (v1_funct_1 @ X19)
% 0.22/0.55          | ~ (v1_relat_1 @ X19))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (((v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.22/0.55        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.55        | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('21', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.22/0.55  thf(t37_relat_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.22/0.55         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (![X15 : $i]:
% 0.22/0.55         (((k2_relat_1 @ X15) = (k1_relat_1 @ (k4_relat_1 @ X15)))
% 0.22/0.55          | ~ (v1_relat_1 @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.22/0.55  thf(t167_relat_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ B ) =>
% 0.22/0.55       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (![X8 : $i, X9 : $i]:
% 0.22/0.55         ((r1_tarski @ (k10_relat_1 @ X8 @ X9) @ (k1_relat_1 @ X8))
% 0.22/0.55          | ~ (v1_relat_1 @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((r1_tarski @ (k10_relat_1 @ (k4_relat_1 @ X0) @ X1) @ 
% 0.22/0.55           (k2_relat_1 @ X0))
% 0.22/0.55          | ~ (v1_relat_1 @ X0)
% 0.22/0.55          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ sk_B)
% 0.22/0.55          | (r1_tarski @ (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ 
% 0.22/0.55             (k2_relat_1 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['21', '24'])).
% 0.22/0.55  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (r1_tarski @ (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ 
% 0.22/0.55          (k2_relat_1 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf(t147_funct_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.55       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.22/0.55         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (![X22 : $i, X23 : $i]:
% 0.22/0.55         (~ (r1_tarski @ X22 @ (k2_relat_1 @ X23))
% 0.22/0.55          | ((k9_relat_1 @ X23 @ (k10_relat_1 @ X23 @ X22)) = (X22))
% 0.22/0.55          | ~ (v1_funct_1 @ X23)
% 0.22/0.55          | ~ (v1_relat_1 @ X23))),
% 0.22/0.55      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ sk_B)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.55          | ((k9_relat_1 @ sk_B @ 
% 0.22/0.55              (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)))
% 0.22/0.55              = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k9_relat_1 @ sk_B @ 
% 0.22/0.55           (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)))
% 0.22/0.55           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k9_relat_1 @ sk_B @ 
% 0.22/0.55            (k10_relat_1 @ (k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B)) @ X0))
% 0.22/0.55            = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 0.22/0.55          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.55          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['15', '32'])).
% 0.22/0.55  thf('34', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.55  thf(t61_funct_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.55       ( ( v2_funct_1 @ A ) =>
% 0.22/0.55         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.22/0.55             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.22/0.55           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.22/0.55             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (![X26 : $i]:
% 0.22/0.55         (~ (v2_funct_1 @ X26)
% 0.22/0.55          | ((k5_relat_1 @ X26 @ (k2_funct_1 @ X26))
% 0.22/0.55              = (k6_relat_1 @ (k1_relat_1 @ X26)))
% 0.22/0.55          | ~ (v1_funct_1 @ X26)
% 0.22/0.55          | ~ (v1_relat_1 @ X26))),
% 0.22/0.55      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      ((((k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))
% 0.22/0.55          = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.55        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.55        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.55        | ~ (v2_funct_1 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.55  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('39', plain, ((v2_funct_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (((k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))
% 0.22/0.55         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.22/0.55  thf(t43_funct_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.55       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (![X24 : $i, X25 : $i]:
% 0.22/0.55         ((k5_relat_1 @ (k6_relat_1 @ X25) @ (k6_relat_1 @ X24))
% 0.22/0.55           = (k6_relat_1 @ (k3_xboole_0 @ X24 @ X25)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.22/0.55  thf(t71_relat_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.55  thf('42', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.22/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.55  thf(t182_relat_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_relat_1 @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( v1_relat_1 @ B ) =>
% 0.22/0.55           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.22/0.55             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i]:
% 0.22/0.55         (~ (v1_relat_1 @ X13)
% 0.22/0.55          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.22/0.55              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 0.22/0.55          | ~ (v1_relat_1 @ X14))),
% 0.22/0.55      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.55          | ~ (v1_relat_1 @ X1)
% 0.22/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.55  thf(fc4_funct_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.55  thf('45', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.55          | ~ (v1_relat_1 @ X1))),
% 0.22/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.55            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['41', '46'])).
% 0.22/0.55  thf('48', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.22/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.55  thf('49', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.22/0.55  thf('50', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.22/0.55      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.22/0.55  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('52', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k9_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.22/0.55           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['33', '40', '50', '51', '52'])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k9_relat_1 @ sk_B @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 0.22/0.55          | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['14', '53'])).
% 0.22/0.55  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((k9_relat_1 @ sk_B @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      (((k9_relat_1 @ sk_B @ sk_A) != (k9_relat_1 @ sk_B @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['7', '56'])).
% 0.22/0.55  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
