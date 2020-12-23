%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PkuzjKfOfK

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 241 expanded)
%              Number of leaves         :   23 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  590 (2127 expanded)
%              Number of equality atoms :   53 ( 158 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X16 ) @ ( k4_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('14',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('15',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X21 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('28',plain,(
    ! [X30: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X30 ) @ X30 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k7_relat_1 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','36'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('47',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','38','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PkuzjKfOfK
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 102 iterations in 0.076s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.51  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.51  thf(t94_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (![X25 : $i, X26 : $i]:
% 0.19/0.51         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 0.19/0.51          | ~ (v1_relat_1 @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.51  thf(t43_funct_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.51       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i]:
% 0.19/0.51        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.51          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.19/0.51         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.19/0.51          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.19/0.51        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.51  thf(fc24_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.19/0.51       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.19/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.51  thf('3', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.19/0.51         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X25 : $i, X26 : $i]:
% 0.19/0.51         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 0.19/0.51          | ~ (v1_relat_1 @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X25 : $i, X26 : $i]:
% 0.19/0.51         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 0.19/0.51          | ~ (v1_relat_1 @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.51  thf(t72_relat_1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X20 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X20)) = (k6_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.19/0.51  thf(t54_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( v1_relat_1 @ B ) =>
% 0.19/0.51           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.51             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X16)
% 0.19/0.51          | ((k4_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 0.19/0.51              = (k5_relat_1 @ (k4_relat_1 @ X16) @ (k4_relat_1 @ X17)))
% 0.19/0.51          | ~ (v1_relat_1 @ X17))),
% 0.19/0.51      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.51            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.19/0.51          | ~ (v1_relat_1 @ X1)
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.51  thf('10', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.51            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.19/0.51          | ~ (v1_relat_1 @ X1))),
% 0.19/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.51            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.19/0.51               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['6', '11'])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X20 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X20)) = (k6_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.19/0.51  thf('14', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('15', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.51           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.19/0.51            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['5', '16'])).
% 0.19/0.51  thf('18', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.19/0.51           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf(t17_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.51  thf(t71_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.51  thf('21', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.19/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.51  thf(t77_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.51         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X21 : $i, X22 : $i]:
% 0.19/0.51         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.19/0.51          | ((k5_relat_1 @ (k6_relat_1 @ X22) @ X21) = (X21))
% 0.19/0.51          | ~ (v1_relat_1 @ X21))),
% 0.19/0.51      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.51          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.19/0.51              = (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('24', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.51          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.19/0.51              = (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.19/0.51           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.19/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['20', '25'])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.51           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.19/0.51  thf('28', plain, (![X30 : $i]: (v4_relat_1 @ (k6_relat_1 @ X30) @ X30)),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf(t209_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X14 : $i, X15 : $i]:
% 0.19/0.51         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.19/0.51          | ~ (v4_relat_1 @ X14 @ X15)
% 0.19/0.51          | ~ (v1_relat_1 @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.51          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.51  thf('31', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.51  thf(t100_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ C ) =>
% 0.19/0.51       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.19/0.51         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.51         (((k7_relat_1 @ (k7_relat_1 @ X11 @ X12) @ X13)
% 0.19/0.51            = (k7_relat_1 @ X11 @ (k3_xboole_0 @ X12 @ X13)))
% 0.19/0.51          | ~ (v1_relat_1 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.19/0.51            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.51  thf('35', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.19/0.51           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.19/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.51      inference('demod', [status(thm)], ['26', '27', '36'])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['19', '37'])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.19/0.51           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.19/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.51      inference('demod', [status(thm)], ['26', '27', '36'])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.51           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.51            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.19/0.51          | ~ (v1_relat_1 @ X1))),
% 0.19/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k4_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.51            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.19/0.51               (k4_relat_1 @ (k6_relat_1 @ X1))))
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['41', '42'])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (![X20 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X20)) = (k6_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (![X20 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X20)) = (k6_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.51           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.51  thf('47', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.19/0.51  thf('48', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.51      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.19/0.51  thf('49', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.19/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.51  thf('50', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.51           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('sup+', [status(thm)], ['48', '49'])).
% 0.19/0.51  thf('51', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.19/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.51  thf('53', plain,
% 0.19/0.51      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.19/0.51         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['4', '38', '52'])).
% 0.19/0.51  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
