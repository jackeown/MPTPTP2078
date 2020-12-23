%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hiXv74Whxs

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:46 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 380 expanded)
%              Number of leaves         :   33 ( 144 expanded)
%              Depth                    :   17
%              Number of atoms          :  836 (3125 expanded)
%              Number of equality atoms :   72 ( 314 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k3_xboole_0 @ X26 @ ( k10_relat_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k1_setfam_1 @ ( k2_tarski @ X26 @ ( k10_relat_1 @ X27 @ X28 ) ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k1_relat_1 @ X32 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X32 @ X31 ) @ X33 )
      | ( r1_tarski @ X31 @ ( k10_relat_1 @ X32 @ X33 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k1_setfam_1 @ ( k2_tarski @ X26 @ ( k10_relat_1 @ X27 @ X28 ) ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k9_relat_1 @ X30 @ ( k10_relat_1 @ X30 @ X29 ) )
        = ( k3_xboole_0 @ X29 @ ( k9_relat_1 @ X30 @ ( k1_relat_1 @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k9_relat_1 @ X30 @ ( k10_relat_1 @ X30 @ X29 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X29 @ ( k9_relat_1 @ X30 @ ( k1_relat_1 @ X30 ) ) ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('46',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X25: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','52','53'])).

thf('55',plain,(
    ! [X25: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','35','36','54','55','56'])).

thf('58',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46','47'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46','47'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hiXv74Whxs
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 407 iterations in 0.214s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.66  thf(t139_funct_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ C ) =>
% 0.46/0.66       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.46/0.66         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.66         (((k10_relat_1 @ (k7_relat_1 @ X27 @ X26) @ X28)
% 0.46/0.66            = (k3_xboole_0 @ X26 @ (k10_relat_1 @ X27 @ X28)))
% 0.46/0.66          | ~ (v1_relat_1 @ X27))),
% 0.46/0.66      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.46/0.66  thf(t12_setfam_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.66         (((k10_relat_1 @ (k7_relat_1 @ X27 @ X26) @ X28)
% 0.46/0.66            = (k1_setfam_1 @ (k2_tarski @ X26 @ (k10_relat_1 @ X27 @ X28))))
% 0.46/0.66          | ~ (v1_relat_1 @ X27))),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf(t175_funct_2, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ![B:$i,C:$i]:
% 0.46/0.66         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.46/0.66           ( ( k10_relat_1 @ A @ C ) =
% 0.46/0.66             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66          ( ![B:$i,C:$i]:
% 0.46/0.66            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.46/0.66              ( ( k10_relat_1 @ A @ C ) =
% 0.46/0.66                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.46/0.66  thf('3', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t148_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ B ) =>
% 0.46/0.66       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.46/0.66          | ~ (v1_relat_1 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.66  thf(t94_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ B ) =>
% 0.46/0.66       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X22 : $i, X23 : $i]:
% 0.46/0.66         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 0.46/0.66          | ~ (v1_relat_1 @ X23))),
% 0.46/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.46/0.66  thf(t43_funct_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.46/0.66       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X34 : $i, X35 : $i]:
% 0.46/0.66         ((k5_relat_1 @ (k6_relat_1 @ X35) @ (k6_relat_1 @ X34))
% 0.46/0.66           = (k6_relat_1 @ (k3_xboole_0 @ X34 @ X35)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X34 : $i, X35 : $i]:
% 0.46/0.66         ((k5_relat_1 @ (k6_relat_1 @ X35) @ (k6_relat_1 @ X34))
% 0.46/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X34 @ X35))))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.66            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.46/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['5', '8'])).
% 0.46/0.66  thf(fc3_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.46/0.66       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.46/0.66  thf('10', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.66  thf(t71_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.66       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.66  thf('12', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.46/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.66            = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.46/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['4', '13'])).
% 0.46/0.66  thf('15', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf(d10_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('18', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.66  thf(t163_funct_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.66       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.66           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.46/0.66         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X31 @ (k1_relat_1 @ X32))
% 0.46/0.66          | ~ (r1_tarski @ (k9_relat_1 @ X32 @ X31) @ X33)
% 0.46/0.66          | (r1_tarski @ X31 @ (k10_relat_1 @ X32 @ X33))
% 0.46/0.66          | ~ (v1_funct_1 @ X32)
% 0.46/0.66          | ~ (v1_relat_1 @ X32))),
% 0.46/0.66      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.46/0.66          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_tarski @ 
% 0.46/0.66             (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))) @ 
% 0.46/0.66             X1)
% 0.46/0.66          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.46/0.66             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.46/0.66          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '20'])).
% 0.46/0.66  thf('22', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.46/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.66  thf(t3_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.66  thf('23', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.66  thf(t48_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.46/0.66           = (k3_xboole_0 @ X10 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ X0)
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['23', '26'])).
% 0.46/0.66  thf(t2_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X8 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '30'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('34', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('36', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.46/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.66         (((k10_relat_1 @ (k7_relat_1 @ X27 @ X26) @ X28)
% 0.46/0.66            = (k1_setfam_1 @ (k2_tarski @ X26 @ (k10_relat_1 @ X27 @ X28))))
% 0.46/0.66          | ~ (v1_relat_1 @ X27))),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf(t148_funct_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.66       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.46/0.66         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X29 : $i, X30 : $i]:
% 0.46/0.66         (((k9_relat_1 @ X30 @ (k10_relat_1 @ X30 @ X29))
% 0.46/0.66            = (k3_xboole_0 @ X29 @ (k9_relat_1 @ X30 @ (k1_relat_1 @ X30))))
% 0.46/0.66          | ~ (v1_funct_1 @ X30)
% 0.46/0.66          | ~ (v1_relat_1 @ X30))),
% 0.46/0.66      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X29 : $i, X30 : $i]:
% 0.46/0.66         (((k9_relat_1 @ X30 @ (k10_relat_1 @ X30 @ X29))
% 0.46/0.66            = (k1_setfam_1 @ 
% 0.46/0.66               (k2_tarski @ X29 @ (k9_relat_1 @ X30 @ (k1_relat_1 @ X30)))))
% 0.46/0.66          | ~ (v1_funct_1 @ X30)
% 0.46/0.66          | ~ (v1_relat_1 @ X30))),
% 0.46/0.66      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.46/0.66            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.46/0.66            = (k1_setfam_1 @ 
% 0.46/0.66               (k2_tarski @ X1 @ 
% 0.46/0.66                (k1_setfam_1 @ 
% 0.46/0.66                 (k2_tarski @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))))
% 0.46/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['38', '41'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf('44', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.46/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('46', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.66  thf('47', plain, (![X25 : $i]: (v1_funct_1 @ (k6_relat_1 @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ 
% 0.46/0.66           (k2_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['42', '43', '44', '45', '46', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0)
% 0.46/0.66            = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.46/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['37', '48'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.66  thf('53', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.46/0.66      inference('demod', [status(thm)], ['49', '52', '53'])).
% 0.46/0.66  thf('55', plain, (![X25 : $i]: (v1_funct_1 @ (k6_relat_1 @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.66  thf('56', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.66          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['21', '22', '35', '36', '54', '55', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.46/0.66        (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['3', '57'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ 
% 0.46/0.66           (k2_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['42', '43', '44', '45', '46', '47'])).
% 0.46/0.66  thf(t17_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.46/0.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X0 : $i, X2 : $i]:
% 0.46/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.46/0.66          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ (k2_tarski @ X14 @ X15)) = (k3_xboole_0 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.46/0.66          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.46/0.66          | ((X0)
% 0.46/0.66              = (k1_setfam_1 @ 
% 0.46/0.66                 (k2_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['59', '65'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k1_setfam_1 @ 
% 0.46/0.66           (k2_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.46/0.66           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['42', '43', '44', '45', '46', '47'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.46/0.66          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (((k10_relat_1 @ sk_A @ sk_C)
% 0.46/0.66         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['58', '68'])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.46/0.66          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['2', '69'])).
% 0.46/0.66  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (((k10_relat_1 @ sk_A @ sk_C)
% 0.46/0.66         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (((k10_relat_1 @ sk_A @ sk_C)
% 0.46/0.66         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('74', plain, ($false),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
