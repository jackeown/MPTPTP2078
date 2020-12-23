%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4KQRvPg3Hs

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:38 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 128 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :   20
%              Number of atoms          :  903 (1470 expanded)
%              Number of equality atoms :   63 ( 103 expanded)
%              Maximal formula depth    :   13 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t127_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X5 @ ( k8_relat_1 @ X6 @ X7 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X3 @ X2 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X2 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X5 @ ( k8_relat_1 @ X6 @ X7 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X4 ) @ X4 )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X3 @ X2 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X2 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X4 ) @ X4 )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X5 @ ( k8_relat_1 @ X6 @ X7 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X5 @ ( k8_relat_1 @ X6 @ X7 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k8_relat_1 @ X3 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X3 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X3 @ X2 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X2 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X3 @ X2 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X2 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X2 ) @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X2 ) @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X5 @ ( k8_relat_1 @ X6 @ X7 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X0 ) ) @ X1 )
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X0 ) ) @ X1 )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X4: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X4 ) @ X4 )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X5 @ ( k8_relat_1 @ X6 @ X7 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X5 @ ( k8_relat_1 @ X6 @ X7 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X3 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k8_relat_1 @ X3 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X3 @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X1 @ X0 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X5 @ ( k8_relat_1 @ X6 @ X7 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf(t128_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) )
        = ( k8_relat_1 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) )
          = ( k8_relat_1 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_relat_1])).

thf('57',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_A @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B )
     != ( k8_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B )
 != ( k8_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_B )
     != ( k8_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ( k8_relat_1 @ sk_A @ sk_B )
 != ( k8_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4KQRvPg3Hs
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:39:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.87/2.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.87/2.09  % Solved by: fo/fo7.sh
% 1.87/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.87/2.09  % done 636 iterations in 1.622s
% 1.87/2.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.87/2.09  % SZS output start Refutation
% 1.87/2.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.87/2.09  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.87/2.09  thf(sk_B_type, type, sk_B: $i).
% 1.87/2.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.87/2.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.87/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.87/2.09  thf(t127_relat_1, axiom,
% 1.87/2.09    (![A:$i,B:$i,C:$i]:
% 1.87/2.09     ( ( v1_relat_1 @ C ) =>
% 1.87/2.09       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 1.87/2.09         ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 1.87/2.09  thf('0', plain,
% 1.87/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X5 @ (k8_relat_1 @ X6 @ X7))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X5 @ X6) @ X7))
% 1.87/2.09          | ~ (v1_relat_1 @ X7))),
% 1.87/2.09      inference('cnf', [status(esa)], [t127_relat_1])).
% 1.87/2.09  thf(t119_relat_1, axiom,
% 1.87/2.09    (![A:$i,B:$i]:
% 1.87/2.09     ( ( v1_relat_1 @ B ) =>
% 1.87/2.09       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 1.87/2.09         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.87/2.09  thf('1', plain,
% 1.87/2.09      (![X2 : $i, X3 : $i]:
% 1.87/2.09         (((k2_relat_1 @ (k8_relat_1 @ X3 @ X2))
% 1.87/2.09            = (k3_xboole_0 @ (k2_relat_1 @ X2) @ X3))
% 1.87/2.09          | ~ (v1_relat_1 @ X2))),
% 1.87/2.09      inference('cnf', [status(esa)], [t119_relat_1])).
% 1.87/2.09  thf('2', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (((k2_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.87/2.09            = (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.87/2.09      inference('sup+', [status(thm)], ['0', '1'])).
% 1.87/2.09  thf(dt_k8_relat_1, axiom,
% 1.87/2.09    (![A:$i,B:$i]:
% 1.87/2.09     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 1.87/2.09  thf('3', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         ((v1_relat_1 @ (k8_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X1))),
% 1.87/2.09      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.87/2.09  thf('4', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k2_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.87/2.09              = (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2)))),
% 1.87/2.09      inference('clc', [status(thm)], ['2', '3'])).
% 1.87/2.09  thf('5', plain,
% 1.87/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X5 @ (k8_relat_1 @ X6 @ X7))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X5 @ X6) @ X7))
% 1.87/2.09          | ~ (v1_relat_1 @ X7))),
% 1.87/2.09      inference('cnf', [status(esa)], [t127_relat_1])).
% 1.87/2.09  thf(t126_relat_1, axiom,
% 1.87/2.09    (![A:$i]:
% 1.87/2.09     ( ( v1_relat_1 @ A ) =>
% 1.87/2.09       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 1.87/2.09  thf('6', plain,
% 1.87/2.09      (![X4 : $i]:
% 1.87/2.09         (((k8_relat_1 @ (k2_relat_1 @ X4) @ X4) = (X4)) | ~ (v1_relat_1 @ X4))),
% 1.87/2.09      inference('cnf', [status(esa)], [t126_relat_1])).
% 1.87/2.09  thf('7', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ 
% 1.87/2.09            (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X1) @ X0)
% 1.87/2.09            = (k8_relat_1 @ X1 @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.87/2.09      inference('sup+', [status(thm)], ['5', '6'])).
% 1.87/2.09  thf('8', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         ((v1_relat_1 @ (k8_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X1))),
% 1.87/2.09      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.87/2.09  thf('9', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ 
% 1.87/2.09              (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X1) @ X0)
% 1.87/2.09              = (k8_relat_1 @ X1 @ X0)))),
% 1.87/2.09      inference('clc', [status(thm)], ['7', '8'])).
% 1.87/2.09  thf('10', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ 
% 1.87/2.09            (k2_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X1 @ X1) @ X0)) @ X0)
% 1.87/2.09            = (k8_relat_1 @ X1 @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['4', '9'])).
% 1.87/2.09  thf('11', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ 
% 1.87/2.09              (k2_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X1 @ X1) @ X0)) @ X0)
% 1.87/2.09              = (k8_relat_1 @ X1 @ X0)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['10'])).
% 1.87/2.09  thf('12', plain,
% 1.87/2.09      (![X2 : $i, X3 : $i]:
% 1.87/2.09         (((k2_relat_1 @ (k8_relat_1 @ X3 @ X2))
% 1.87/2.09            = (k3_xboole_0 @ (k2_relat_1 @ X2) @ X3))
% 1.87/2.09          | ~ (v1_relat_1 @ X2))),
% 1.87/2.09      inference('cnf', [status(esa)], [t119_relat_1])).
% 1.87/2.09  thf('13', plain,
% 1.87/2.09      (![X4 : $i]:
% 1.87/2.09         (((k8_relat_1 @ (k2_relat_1 @ X4) @ X4) = (X4)) | ~ (v1_relat_1 @ X4))),
% 1.87/2.09      inference('cnf', [status(esa)], [t126_relat_1])).
% 1.87/2.09  thf('14', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ 
% 1.87/2.09            (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1))
% 1.87/2.09          | ~ (v1_relat_1 @ X1)
% 1.87/2.09          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 1.87/2.09      inference('sup+', [status(thm)], ['12', '13'])).
% 1.87/2.09  thf('15', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         ((v1_relat_1 @ (k8_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X1))),
% 1.87/2.09      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.87/2.09  thf('16', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X1)
% 1.87/2.09          | ((k8_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ 
% 1.87/2.09              (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1)))),
% 1.87/2.09      inference('clc', [status(thm)], ['14', '15'])).
% 1.87/2.09  thf('17', plain,
% 1.87/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X5 @ (k8_relat_1 @ X6 @ X7))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X5 @ X6) @ X7))
% 1.87/2.09          | ~ (v1_relat_1 @ X7))),
% 1.87/2.09      inference('cnf', [status(esa)], [t127_relat_1])).
% 1.87/2.09  thf('18', plain,
% 1.87/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X5 @ (k8_relat_1 @ X6 @ X7))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X5 @ X6) @ X7))
% 1.87/2.09          | ~ (v1_relat_1 @ X7))),
% 1.87/2.09      inference('cnf', [status(esa)], [t127_relat_1])).
% 1.87/2.09  thf('19', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X3 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0)))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.87/2.09      inference('sup+', [status(thm)], ['17', '18'])).
% 1.87/2.09  thf('20', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         ((v1_relat_1 @ (k8_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X1))),
% 1.87/2.09      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 1.87/2.09  thf('21', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ X3 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.87/2.09              = (k8_relat_1 @ (k3_xboole_0 @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))))),
% 1.87/2.09      inference('clc', [status(thm)], ['19', '20'])).
% 1.87/2.09  thf('22', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 1.87/2.09            (k8_relat_1 @ (k3_xboole_0 @ X1 @ X1) @ X0))
% 1.87/2.09            = (k8_relat_1 @ X1 @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['16', '21'])).
% 1.87/2.09  thf('23', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 1.87/2.09              (k8_relat_1 @ (k3_xboole_0 @ X1 @ X1) @ X0))
% 1.87/2.09              = (k8_relat_1 @ X1 @ X0)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['22'])).
% 1.87/2.09  thf('24', plain,
% 1.87/2.09      (![X2 : $i, X3 : $i]:
% 1.87/2.09         (((k2_relat_1 @ (k8_relat_1 @ X3 @ X2))
% 1.87/2.09            = (k3_xboole_0 @ (k2_relat_1 @ X2) @ X3))
% 1.87/2.09          | ~ (v1_relat_1 @ X2))),
% 1.87/2.09      inference('cnf', [status(esa)], [t119_relat_1])).
% 1.87/2.09  thf('25', plain,
% 1.87/2.09      (![X2 : $i, X3 : $i]:
% 1.87/2.09         (((k2_relat_1 @ (k8_relat_1 @ X3 @ X2))
% 1.87/2.09            = (k3_xboole_0 @ (k2_relat_1 @ X2) @ X3))
% 1.87/2.09          | ~ (v1_relat_1 @ X2))),
% 1.87/2.09      inference('cnf', [status(esa)], [t119_relat_1])).
% 1.87/2.09  thf('26', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k2_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.87/2.09              = (k3_xboole_0 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2)))),
% 1.87/2.09      inference('clc', [status(thm)], ['2', '3'])).
% 1.87/2.09  thf('27', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (((k2_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X0) @ X1))
% 1.87/2.09            = (k3_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X2))
% 1.87/2.09          | ~ (v1_relat_1 @ X1)
% 1.87/2.09          | ~ (v1_relat_1 @ X1))),
% 1.87/2.09      inference('sup+', [status(thm)], ['25', '26'])).
% 1.87/2.09  thf('28', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X1)
% 1.87/2.09          | ((k2_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X0) @ X1))
% 1.87/2.09              = (k3_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X2)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['27'])).
% 1.87/2.09  thf('29', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (((k3_xboole_0 @ (k2_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 1.87/2.09            = (k3_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ X2) @ X0) @ X1))
% 1.87/2.09          | ~ (v1_relat_1 @ X2)
% 1.87/2.09          | ~ (v1_relat_1 @ X2))),
% 1.87/2.09      inference('sup+', [status(thm)], ['24', '28'])).
% 1.87/2.09  thf('30', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X2)
% 1.87/2.09          | ((k3_xboole_0 @ (k2_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 1.87/2.09              = (k3_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ X2) @ X0) @ X1)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['29'])).
% 1.87/2.09  thf('31', plain,
% 1.87/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X5 @ (k8_relat_1 @ X6 @ X7))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X5 @ X6) @ X7))
% 1.87/2.09          | ~ (v1_relat_1 @ X7))),
% 1.87/2.09      inference('cnf', [status(esa)], [t127_relat_1])).
% 1.87/2.09  thf('32', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X1)
% 1.87/2.09          | ((k8_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ 
% 1.87/2.09              (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1)))),
% 1.87/2.09      inference('clc', [status(thm)], ['14', '15'])).
% 1.87/2.09  thf('33', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ 
% 1.87/2.09            (k3_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1) @ X1) @ X0)
% 1.87/2.09            = (k8_relat_1 @ X1 @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['31', '32'])).
% 1.87/2.09  thf('34', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ 
% 1.87/2.09              (k3_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1) @ X1) @ X0)
% 1.87/2.09              = (k8_relat_1 @ X1 @ X0)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['33'])).
% 1.87/2.09  thf('35', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ 
% 1.87/2.09            (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X0)) @ X1)
% 1.87/2.09            = (k8_relat_1 @ X0 @ X1))
% 1.87/2.09          | ~ (v1_relat_1 @ X1)
% 1.87/2.09          | ~ (v1_relat_1 @ X1))),
% 1.87/2.09      inference('sup+', [status(thm)], ['30', '34'])).
% 1.87/2.09  thf('36', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X1)
% 1.87/2.09          | ((k8_relat_1 @ 
% 1.87/2.09              (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X0)) @ X1)
% 1.87/2.09              = (k8_relat_1 @ X0 @ X1)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['35'])).
% 1.87/2.09  thf('37', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X1)
% 1.87/2.09          | ((k2_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X0) @ X1))
% 1.87/2.09              = (k3_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X2)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['27'])).
% 1.87/2.09  thf('38', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k2_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.87/2.09            = (k3_xboole_0 @ 
% 1.87/2.09               (k3_xboole_0 @ (k2_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X1)) @ 
% 1.87/2.09               (k2_relat_1 @ X0)))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['36', '37'])).
% 1.87/2.09  thf('39', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.87/2.09              = (k3_xboole_0 @ 
% 1.87/2.09                 (k3_xboole_0 @ (k2_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X1)) @ 
% 1.87/2.09                 (k2_relat_1 @ X0))))),
% 1.87/2.09      inference('simplify', [status(thm)], ['38'])).
% 1.87/2.09  thf('40', plain,
% 1.87/2.09      (![X4 : $i]:
% 1.87/2.09         (((k8_relat_1 @ (k2_relat_1 @ X4) @ X4) = (X4)) | ~ (v1_relat_1 @ X4))),
% 1.87/2.09      inference('cnf', [status(esa)], [t126_relat_1])).
% 1.87/2.09  thf('41', plain,
% 1.87/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X5 @ (k8_relat_1 @ X6 @ X7))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X5 @ X6) @ X7))
% 1.87/2.09          | ~ (v1_relat_1 @ X7))),
% 1.87/2.09      inference('cnf', [status(esa)], [t127_relat_1])).
% 1.87/2.09  thf('42', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X1 @ X0)
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)) @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['40', '41'])).
% 1.87/2.09  thf('43', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ X1 @ X0)
% 1.87/2.09              = (k8_relat_1 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)) @ X0)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['42'])).
% 1.87/2.09  thf('44', plain,
% 1.87/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X5 @ (k8_relat_1 @ X6 @ X7))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X5 @ X6) @ X7))
% 1.87/2.09          | ~ (v1_relat_1 @ X7))),
% 1.87/2.09      inference('cnf', [status(esa)], [t127_relat_1])).
% 1.87/2.09  thf('45', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ X3 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.87/2.09              = (k8_relat_1 @ (k3_xboole_0 @ X3 @ X2) @ (k8_relat_1 @ X1 @ X0))))),
% 1.87/2.09      inference('clc', [status(thm)], ['19', '20'])).
% 1.87/2.09  thf('46', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X3 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X3 @ X2) @ X1) @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['44', '45'])).
% 1.87/2.09  thf('47', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ X3 @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.87/2.09              = (k8_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X3 @ X2) @ X1) @ X0)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['46'])).
% 1.87/2.09  thf('48', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 1.87/2.09            = (k8_relat_1 @ 
% 1.87/2.09               (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k2_relat_1 @ X0)) @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['43', '47'])).
% 1.87/2.09  thf('49', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 1.87/2.09              = (k8_relat_1 @ 
% 1.87/2.09                 (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k2_relat_1 @ X0)) @ 
% 1.87/2.09                 X0)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['48'])).
% 1.87/2.09  thf('50', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 1.87/2.09            (k8_relat_1 @ (k3_xboole_0 @ X1 @ X1) @ X0))
% 1.87/2.09            = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['39', '49'])).
% 1.87/2.09  thf('51', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ (k2_relat_1 @ X0) @ 
% 1.87/2.09              (k8_relat_1 @ (k3_xboole_0 @ X1 @ X1) @ X0))
% 1.87/2.09              = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['50'])).
% 1.87/2.09  thf('52', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X1 @ X0)
% 1.87/2.09            = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['23', '51'])).
% 1.87/2.09  thf('53', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ X1 @ X0)
% 1.87/2.09              = (k8_relat_1 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X0)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['52'])).
% 1.87/2.09  thf('54', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (((k8_relat_1 @ (k3_xboole_0 @ X1 @ X1) @ X0) = (k8_relat_1 @ X1 @ X0))
% 1.87/2.09          | ~ (v1_relat_1 @ X0)
% 1.87/2.09          | ~ (v1_relat_1 @ X0))),
% 1.87/2.09      inference('sup+', [status(thm)], ['11', '53'])).
% 1.87/2.09  thf('55', plain,
% 1.87/2.09      (![X0 : $i, X1 : $i]:
% 1.87/2.09         (~ (v1_relat_1 @ X0)
% 1.87/2.09          | ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X1) @ X0)
% 1.87/2.09              = (k8_relat_1 @ X1 @ X0)))),
% 1.87/2.09      inference('simplify', [status(thm)], ['54'])).
% 1.87/2.09  thf('56', plain,
% 1.87/2.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.87/2.09         (((k8_relat_1 @ X5 @ (k8_relat_1 @ X6 @ X7))
% 1.87/2.09            = (k8_relat_1 @ (k3_xboole_0 @ X5 @ X6) @ X7))
% 1.87/2.09          | ~ (v1_relat_1 @ X7))),
% 1.87/2.09      inference('cnf', [status(esa)], [t127_relat_1])).
% 1.87/2.09  thf(t128_relat_1, conjecture,
% 1.87/2.09    (![A:$i,B:$i]:
% 1.87/2.09     ( ( v1_relat_1 @ B ) =>
% 1.87/2.09       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) ) = ( k8_relat_1 @ A @ B ) ) ))).
% 1.87/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.87/2.09    (~( ![A:$i,B:$i]:
% 1.87/2.09        ( ( v1_relat_1 @ B ) =>
% 1.87/2.09          ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) ) =
% 1.87/2.09            ( k8_relat_1 @ A @ B ) ) ) )),
% 1.87/2.09    inference('cnf.neg', [status(esa)], [t128_relat_1])).
% 1.87/2.09  thf('57', plain,
% 1.87/2.09      (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_A @ sk_B))
% 1.87/2.09         != (k8_relat_1 @ sk_A @ sk_B))),
% 1.87/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.09  thf('58', plain,
% 1.87/2.09      ((((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B)
% 1.87/2.09          != (k8_relat_1 @ sk_A @ sk_B))
% 1.87/2.09        | ~ (v1_relat_1 @ sk_B))),
% 1.87/2.09      inference('sup-', [status(thm)], ['56', '57'])).
% 1.87/2.09  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 1.87/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.09  thf('60', plain,
% 1.87/2.09      (((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B)
% 1.87/2.09         != (k8_relat_1 @ sk_A @ sk_B))),
% 1.87/2.09      inference('demod', [status(thm)], ['58', '59'])).
% 1.87/2.09  thf('61', plain,
% 1.87/2.09      ((((k8_relat_1 @ sk_A @ sk_B) != (k8_relat_1 @ sk_A @ sk_B))
% 1.87/2.09        | ~ (v1_relat_1 @ sk_B))),
% 1.87/2.09      inference('sup-', [status(thm)], ['55', '60'])).
% 1.87/2.09  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 1.87/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.87/2.09  thf('63', plain,
% 1.87/2.09      (((k8_relat_1 @ sk_A @ sk_B) != (k8_relat_1 @ sk_A @ sk_B))),
% 1.87/2.09      inference('demod', [status(thm)], ['61', '62'])).
% 1.87/2.09  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 1.87/2.09  
% 1.87/2.09  % SZS output end Refutation
% 1.87/2.09  
% 1.87/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
