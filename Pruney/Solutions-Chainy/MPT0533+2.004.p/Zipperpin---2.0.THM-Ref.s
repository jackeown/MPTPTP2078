%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pa21gjOgfe

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:44 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 134 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   20
%              Number of atoms          :  633 (1211 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t133_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t133_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k8_relat_1 @ X17 @ X18 ) @ ( k8_relat_1 @ X17 @ X16 ) )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( ( k8_relat_1 @ X14 @ ( k8_relat_1 @ X13 @ X15 ) )
        = ( k8_relat_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X11 @ X12 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X11 @ X12 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X11 @ X12 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X3 @ ( k8_relat_1 @ X2 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C ) ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C ) ) @ sk_D )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ sk_D @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C ) ) )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k3_xboole_0 @ sk_D @ ( k8_relat_1 @ sk_A @ sk_C ) )
      = ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','37'])).

thf('39',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k8_relat_1 @ X0 @ sk_C ) @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D @ ( k8_relat_1 @ X0 @ sk_C ) )
      = ( k8_relat_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k8_relat_1 @ sk_A @ sk_C )
    = ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','47','48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X11 @ X12 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k8_relat_1 @ X17 @ X18 ) @ ( k8_relat_1 @ X17 @ X16 ) )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('60',plain,
    ( ( k2_xboole_0 @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_C ) )
    = ( k8_relat_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k8_relat_1 @ sk_B @ sk_C ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['6','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pa21gjOgfe
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 135 iterations in 0.125s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.39/0.58  thf(t133_relat_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ C ) =>
% 0.39/0.58       ( ![D:$i]:
% 0.39/0.58         ( ( v1_relat_1 @ D ) =>
% 0.39/0.58           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.39/0.58             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.58        ( ( v1_relat_1 @ C ) =>
% 0.39/0.58          ( ![D:$i]:
% 0.39/0.58            ( ( v1_relat_1 @ D ) =>
% 0.39/0.58              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.39/0.58                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t132_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ B ) =>
% 0.39/0.58       ( ![C:$i]:
% 0.39/0.58         ( ( v1_relat_1 @ C ) =>
% 0.39/0.58           ( ( r1_tarski @ B @ C ) =>
% 0.39/0.58             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X16)
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ X17 @ X18) @ (k8_relat_1 @ X17 @ X16))
% 0.39/0.58          | ~ (r1_tarski @ X18 @ X16)
% 0.39/0.58          | ~ (v1_relat_1 @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [t132_relat_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ sk_C)
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ (k8_relat_1 @ X0 @ sk_D))
% 0.39/0.58          | ~ (v1_relat_1 @ sk_D))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('5', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ (k8_relat_1 @ X0 @ sk_D))),
% 0.39/0.58      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.39/0.58  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t129_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ C ) =>
% 0.39/0.58       ( ( r1_tarski @ A @ B ) =>
% 0.39/0.58         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X13 @ X14)
% 0.39/0.58          | ~ (v1_relat_1 @ X15)
% 0.39/0.58          | ((k8_relat_1 @ X14 @ (k8_relat_1 @ X13 @ X15))
% 0.39/0.58              = (k8_relat_1 @ X13 @ X15)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.39/0.58            = (k8_relat_1 @ sk_A @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('10', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t117_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         ((r1_tarski @ (k8_relat_1 @ X11 @ X12) @ X12) | ~ (v1_relat_1 @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         ((r1_tarski @ (k8_relat_1 @ X11 @ X12) @ X12) | ~ (v1_relat_1 @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.39/0.58  thf(t12_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i]:
% 0.39/0.58         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ((k2_xboole_0 @ (k8_relat_1 @ X1 @ X0) @ X0) = (X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf(t11_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.58         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ X2 @ X0) @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['11', '16'])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         ((r1_tarski @ (k8_relat_1 @ X11 @ X12) @ X12) | ~ (v1_relat_1 @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.39/0.58  thf(t28_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ((k3_xboole_0 @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.39/0.58              = (k8_relat_1 @ X1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ((k3_xboole_0 @ X0 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.58              = (k8_relat_1 @ X1 @ X0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['20', '21'])).
% 0.39/0.58  thf(fc1_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X9 : $i, X10 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('clc', [status(thm)], ['17', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i]:
% 0.39/0.58         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ((k2_xboole_0 @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X0)
% 0.39/0.58              = (X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.58         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ X3 @ (k8_relat_1 @ X2 @ X0)) @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C)) @ sk_D)
% 0.39/0.58          | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '30'])).
% 0.39/0.58  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C)) @ sk_D)),
% 0.39/0.58      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k3_xboole_0 @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C)) @ sk_D)
% 0.39/0.58           = (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k3_xboole_0 @ sk_D @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C)))
% 0.39/0.58           = (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      ((((k3_xboole_0 @ sk_D @ (k8_relat_1 @ sk_A @ sk_C))
% 0.39/0.58          = (k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C)))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup+', [status(thm)], ['9', '37'])).
% 0.39/0.58  thf('39', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ X2 @ X0) @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ sk_D) | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.58  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('43', plain, (![X0 : $i]: (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ sk_D)),
% 0.39/0.58      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((k3_xboole_0 @ (k8_relat_1 @ X0 @ sk_C) @ sk_D)
% 0.39/0.58           = (k8_relat_1 @ X0 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((k3_xboole_0 @ sk_D @ (k8_relat_1 @ X0 @ sk_C))
% 0.39/0.58           = (k8_relat_1 @ X0 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.58  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (((k8_relat_1 @ sk_A @ sk_C)
% 0.39/0.58         = (k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['38', '47', '48'])).
% 0.39/0.58  thf('50', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         ((r1_tarski @ (k8_relat_1 @ X11 @ X12) @ X12) | ~ (v1_relat_1 @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X16)
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ X17 @ X18) @ (k8_relat_1 @ X17 @ X16))
% 0.39/0.58          | ~ (r1_tarski @ X18 @ X16)
% 0.39/0.58          | ~ (v1_relat_1 @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [t132_relat_1])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.39/0.58             (k8_relat_1 @ X2 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.39/0.58           (k8_relat_1 @ X2 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['52'])).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.39/0.58             (k8_relat_1 @ X2 @ X0)))),
% 0.39/0.58      inference('clc', [status(thm)], ['53', '54'])).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      (((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_C))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup+', [status(thm)], ['49', '55'])).
% 0.39/0.58  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.39/0.58  thf('59', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i]:
% 0.39/0.58         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.58  thf('60', plain,
% 0.39/0.58      (((k2_xboole_0 @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_C))
% 0.39/0.58         = (k8_relat_1 @ sk_B @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.58         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.39/0.58  thf('62', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r1_tarski @ (k8_relat_1 @ sk_B @ sk_C) @ X0)
% 0.39/0.58          | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '62'])).
% 0.39/0.58  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
