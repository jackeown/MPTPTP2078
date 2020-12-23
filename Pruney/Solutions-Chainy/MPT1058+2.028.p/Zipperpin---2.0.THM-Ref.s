%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7GsWY0tP0d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 118 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  613 ( 884 expanded)
%              Number of equality atoms :   53 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

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

thf('4',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X2
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('22',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k7_relat_1 @ X25 @ X26 )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k7_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X23 ) @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ ( k6_relat_1 @ X32 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ ( k6_relat_1 @ X32 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = X0 ) ),
    inference(demod,[status(thm)],['21','41'])).

thf('43',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['2','42'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['43','47'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('49',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k3_xboole_0 @ X29 @ ( k10_relat_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k1_setfam_1 @ ( k2_tarski @ X29 @ ( k10_relat_1 @ X30 @ X31 ) ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7GsWY0tP0d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 141 iterations in 0.072s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(t48_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.21/0.53           = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf(t12_setfam_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.21/0.53           = (k1_setfam_1 @ (k2_tarski @ X13 @ X14)))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf(t7_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.53  thf(t175_funct_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.53           ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.53             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.53          ( ![B:$i,C:$i]:
% 0.21/0.53            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.53              ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.53                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.21/0.53  thf('4', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t1_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.53       ( r1_tarski @ A @ C ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X7 @ X8)
% 0.21/0.53          | ~ (r1_tarski @ X8 @ X9)
% 0.21/0.53          | (r1_tarski @ X7 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.53          | ~ (r1_tarski @ sk_B @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.53  thf(t43_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.21/0.53       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.53         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.21/0.53          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (r1_tarski @ (k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B) @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.53         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.21/0.53          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X2 : $i, X4 : $i]:
% 0.21/0.53         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 0.21/0.53          | ((X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 0.21/0.53          | ((X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 0.21/0.53          | ((X2) = (k4_xboole_0 @ X1 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X1 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.53           = (k4_xboole_0 @ X1 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.21/0.53           = (k1_setfam_1 @ (k2_tarski @ X13 @ X14)))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X0 @ 
% 0.21/0.53           (k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.21/0.53           = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf(t71_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.53       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.53  thf('22', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('24', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.53  thf(t97_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.53         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X25 : $i, X26 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.21/0.53          | ((k7_relat_1 @ X25 @ X26) = (X25))
% 0.21/0.53          | ~ (v1_relat_1 @ X25))),
% 0.21/0.53      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['22', '26'])).
% 0.21/0.53  thf(fc3_funct_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.53       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('28', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf(t94_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i]:
% 0.21/0.53         (((k7_relat_1 @ X24 @ X23) = (k5_relat_1 @ (k6_relat_1 @ X23) @ X24))
% 0.21/0.53          | ~ (v1_relat_1 @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.53  thf(t43_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.53       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X32 : $i, X33 : $i]:
% 0.21/0.53         ((k5_relat_1 @ (k6_relat_1 @ X33) @ (k6_relat_1 @ X32))
% 0.21/0.53           = (k6_relat_1 @ (k3_xboole_0 @ X32 @ X33)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X32 : $i, X33 : $i]:
% 0.21/0.53         ((k5_relat_1 @ (k6_relat_1 @ X33) @ (k6_relat_1 @ X32))
% 0.21/0.53           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X32 @ X33))))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.53            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.21/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['30', '33'])).
% 0.21/0.53  thf('35', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.53           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))
% 0.21/0.53           = (k6_relat_1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '36'])).
% 0.21/0.53  thf('38', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.53           = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.53  thf('40', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X0 @ 
% 0.21/0.53           (k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)) = (X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.21/0.53         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.21/0.53      inference('sup+', [status(thm)], ['2', '42'])).
% 0.21/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.21/0.53           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.21/0.53         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['43', '47'])).
% 0.21/0.53  thf(t139_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.53         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.53         (((k10_relat_1 @ (k7_relat_1 @ X30 @ X29) @ X31)
% 0.21/0.53            = (k3_xboole_0 @ X29 @ (k10_relat_1 @ X30 @ X31)))
% 0.21/0.53          | ~ (v1_relat_1 @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.53         (((k10_relat_1 @ (k7_relat_1 @ X30 @ X29) @ X31)
% 0.21/0.53            = (k1_setfam_1 @ (k2_tarski @ X29 @ (k10_relat_1 @ X30 @ X31))))
% 0.21/0.53          | ~ (v1_relat_1 @ X30))),
% 0.21/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.53         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.53          != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.53         != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.21/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['48', '55'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
