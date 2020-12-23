%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nnweWLBIy7

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 238 expanded)
%              Number of leaves         :   24 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  623 (1960 expanded)
%              Number of equality atoms :   60 ( 192 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

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

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ( ( k7_relat_1 @ X24 @ X25 )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X37 ) @ ( k6_relat_1 @ X36 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = ( k3_xboole_0 @ X31 @ ( k9_relat_1 @ X32 @ ( k1_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('28',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ( ( k7_relat_1 @ X24 @ X25 )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','38','39','40'])).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','38','39','40'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['17','52'])).

thf('54',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('55',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nnweWLBIy7
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:44:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 271 iterations in 0.152s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(t139_funct_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ C ) =>
% 0.21/0.59       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.59         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.59         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 0.21/0.59            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 0.21/0.59          | ~ (v1_relat_1 @ X29))),
% 0.21/0.59      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.59  thf(t175_funct_2, conjecture,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.59       ( ![B:$i,C:$i]:
% 0.21/0.59         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.59           ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.59             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i]:
% 0.21/0.59        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.59          ( ![B:$i,C:$i]:
% 0.21/0.59            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.59              ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.59                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.21/0.59  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t71_relat_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.59  thf('2', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.21/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.59  thf(t97_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ B ) =>
% 0.21/0.59       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.59         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (![X24 : $i, X25 : $i]:
% 0.21/0.59         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.21/0.59          | ((k7_relat_1 @ X24 @ X25) = (X24))
% 0.21/0.59          | ~ (v1_relat_1 @ X24))),
% 0.21/0.59      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.59  thf('4', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.59          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.59  thf(fc3_funct_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.59       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.59  thf('5', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.59          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.21/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (((k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)
% 0.21/0.59         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.59  thf(t94_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ B ) =>
% 0.21/0.59       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.59  thf('8', plain,
% 0.21/0.59      (![X22 : $i, X23 : $i]:
% 0.21/0.59         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 0.21/0.59          | ~ (v1_relat_1 @ X23))),
% 0.21/0.59      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.59  thf(t43_funct_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.59       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (![X36 : $i, X37 : $i]:
% 0.21/0.59         ((k5_relat_1 @ (k6_relat_1 @ X37) @ (k6_relat_1 @ X36))
% 0.21/0.59           = (k6_relat_1 @ (k3_xboole_0 @ X36 @ X37)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.59            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.59  thf('11', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.59           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.59  thf('13', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.21/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.59  thf('14', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.59           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.59  thf('15', plain,
% 0.21/0.59      (((k1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.21/0.59         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.21/0.59      inference('sup+', [status(thm)], ['7', '14'])).
% 0.21/0.59  thf('16', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.21/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.59  thf('17', plain,
% 0.21/0.59      (((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.59         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.59  thf(t148_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ B ) =>
% 0.21/0.59       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.59  thf('18', plain,
% 0.21/0.59      (![X16 : $i, X17 : $i]:
% 0.21/0.59         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.21/0.59          | ~ (v1_relat_1 @ X16))),
% 0.21/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.59  thf('19', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.59           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.59  thf('20', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.21/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.59  thf('21', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.59           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.59  thf('22', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['18', '21'])).
% 0.21/0.59  thf('23', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.59  thf(t148_funct_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.59       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.21/0.59         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.21/0.59  thf('25', plain,
% 0.21/0.59      (![X31 : $i, X32 : $i]:
% 0.21/0.59         (((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31))
% 0.21/0.59            = (k3_xboole_0 @ X31 @ (k9_relat_1 @ X32 @ (k1_relat_1 @ X32))))
% 0.21/0.59          | ~ (v1_funct_1 @ X32)
% 0.21/0.59          | ~ (v1_relat_1 @ X32))),
% 0.21/0.59      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.21/0.59  thf('26', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.21/0.59            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.21/0.59            = (k3_xboole_0 @ X1 @ 
% 0.21/0.59               (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))
% 0.21/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.59          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.59  thf('27', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.59  thf('28', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.21/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.59  thf(d10_xboole_0, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.59  thf('29', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.59  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.59  thf('31', plain,
% 0.21/0.59      (![X24 : $i, X25 : $i]:
% 0.21/0.59         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.21/0.59          | ((k7_relat_1 @ X24 @ X25) = (X24))
% 0.21/0.59          | ~ (v1_relat_1 @ X24))),
% 0.21/0.59      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.59  thf('32', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.59  thf('33', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.59           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.59  thf('34', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.59            = (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.21/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.59  thf('35', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.21/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.59  thf('36', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.21/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.59  thf('37', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.59  thf('38', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.21/0.59  thf('39', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.59  thf('40', plain, (![X27 : $i]: (v1_funct_1 @ (k6_relat_1 @ X27))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.59  thf('41', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.21/0.59           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['26', '27', '28', '38', '39', '40'])).
% 0.21/0.59  thf('42', plain,
% 0.21/0.59      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.59         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 0.21/0.59            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 0.21/0.59          | ~ (v1_relat_1 @ X29))),
% 0.21/0.59      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.59  thf('43', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.21/0.59           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['26', '27', '28', '38', '39', '40'])).
% 0.21/0.59  thf('44', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0)
% 0.21/0.59            = (k3_xboole_0 @ X0 @ X1))
% 0.21/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.59  thf('45', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.21/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.59  thf('46', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.59  thf('47', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['45', '46'])).
% 0.21/0.59  thf('48', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.59  thf('49', plain,
% 0.21/0.59      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.59  thf('50', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.59  thf('51', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.59      inference('demod', [status(thm)], ['44', '49', '50'])).
% 0.21/0.59  thf('52', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.59           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['41', '51'])).
% 0.21/0.59  thf('53', plain,
% 0.21/0.59      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.21/0.59         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.21/0.59      inference('sup+', [status(thm)], ['17', '52'])).
% 0.21/0.59  thf('54', plain,
% 0.21/0.59      (((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.59         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.59  thf('55', plain,
% 0.21/0.59      (((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.59         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.59  thf('56', plain,
% 0.21/0.59      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.59          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.21/0.59        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.59      inference('sup+', [status(thm)], ['0', '55'])).
% 0.21/0.59  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('58', plain,
% 0.21/0.59      (((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.59         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.59      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.59  thf('59', plain,
% 0.21/0.59      (((k10_relat_1 @ sk_A @ sk_C)
% 0.21/0.59         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('60', plain, ($false),
% 0.21/0.59      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.21/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
