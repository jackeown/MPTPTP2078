%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r1gV0Sz646

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:56 EST 2020

% Result     : Theorem 9.82s
% Output     : Refutation 9.82s
% Verified   : 
% Statistics : Number of formulae       :  130 (1321 expanded)
%              Number of leaves         :   30 ( 468 expanded)
%              Depth                    :   16
%              Number of atoms          : 1125 (11464 expanded)
%              Number of equality atoms :   87 ( 910 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k8_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ X25 @ ( k6_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

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
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('5',plain,(
    ! [X36: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X36 ) ) @ X36 )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k8_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ X25 @ ( k6_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k8_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ X25 @ ( k6_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k5_relat_1 @ X30 @ ( k5_relat_1 @ X29 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k8_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ X25 @ ( k6_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('17',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X36: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X36 ) ) @ X36 )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k5_relat_1 @ X30 @ ( k5_relat_1 @ X29 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X39 @ X40 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X39 ) @ X40 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k8_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ X25 @ ( k6_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('44',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k7_relat_1 @ X42 @ X41 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X41 ) @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','48'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('50',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X34 )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('53',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k8_relat_1 @ X28 @ X27 )
        = ( k3_xboole_0 @ X27 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X27 ) @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','63'])).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k8_relat_1 @ X28 @ X27 )
        = ( k3_xboole_0 @ X27 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X27 ) @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('66',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ X0 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','48'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','62'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('74',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('75',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','62'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','62'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','48'])).

thf('89',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','81','86','87','88','89'])).

thf('91',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','81','86','87','88','89'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','81','86','87','88','89'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('98',plain,(
    $false ),
    inference(simplify,[status(thm)],['97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r1gV0Sz646
% 0.14/0.37  % Computer   : n023.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:42:36 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 9.82/10.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.82/10.09  % Solved by: fo/fo7.sh
% 9.82/10.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.82/10.09  % done 7099 iterations in 9.632s
% 9.82/10.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.82/10.09  % SZS output start Refutation
% 9.82/10.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.82/10.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.82/10.09  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 9.82/10.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.82/10.09  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.82/10.09  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 9.82/10.09  thf(sk_A_type, type, sk_A: $i).
% 9.82/10.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.82/10.09  thf(sk_B_type, type, sk_B: $i).
% 9.82/10.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.82/10.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.82/10.09  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 9.82/10.09  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.82/10.09  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 9.82/10.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.82/10.09  thf(t123_relat_1, axiom,
% 9.82/10.09    (![A:$i,B:$i]:
% 9.82/10.09     ( ( v1_relat_1 @ B ) =>
% 9.82/10.09       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 9.82/10.09  thf('0', plain,
% 9.82/10.09      (![X25 : $i, X26 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X26 @ X25) = (k5_relat_1 @ X25 @ (k6_relat_1 @ X26)))
% 9.82/10.09          | ~ (v1_relat_1 @ X25))),
% 9.82/10.09      inference('cnf', [status(esa)], [t123_relat_1])).
% 9.82/10.09  thf(t43_funct_1, conjecture,
% 9.82/10.09    (![A:$i,B:$i]:
% 9.82/10.09     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 9.82/10.09       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.82/10.09  thf(zf_stmt_0, negated_conjecture,
% 9.82/10.09    (~( ![A:$i,B:$i]:
% 9.82/10.09        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 9.82/10.09          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 9.82/10.09    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 9.82/10.09  thf('1', plain,
% 9.82/10.09      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 9.82/10.09         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 9.82/10.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.09  thf('2', plain,
% 9.82/10.09      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 9.82/10.09          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 9.82/10.09        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 9.82/10.09      inference('sup-', [status(thm)], ['0', '1'])).
% 9.82/10.09  thf(fc3_funct_1, axiom,
% 9.82/10.09    (![A:$i]:
% 9.82/10.09     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 9.82/10.09       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 9.82/10.09  thf('3', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('4', plain,
% 9.82/10.09      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 9.82/10.09         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 9.82/10.09      inference('demod', [status(thm)], ['2', '3'])).
% 9.82/10.09  thf(t78_relat_1, axiom,
% 9.82/10.09    (![A:$i]:
% 9.82/10.09     ( ( v1_relat_1 @ A ) =>
% 9.82/10.09       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 9.82/10.09  thf('5', plain,
% 9.82/10.09      (![X36 : $i]:
% 9.82/10.09         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X36)) @ X36) = (X36))
% 9.82/10.09          | ~ (v1_relat_1 @ X36))),
% 9.82/10.09      inference('cnf', [status(esa)], [t78_relat_1])).
% 9.82/10.09  thf('6', plain,
% 9.82/10.09      (![X25 : $i, X26 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X26 @ X25) = (k5_relat_1 @ X25 @ (k6_relat_1 @ X26)))
% 9.82/10.09          | ~ (v1_relat_1 @ X25))),
% 9.82/10.09      inference('cnf', [status(esa)], [t123_relat_1])).
% 9.82/10.09  thf('7', plain,
% 9.82/10.09      (![X25 : $i, X26 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X26 @ X25) = (k5_relat_1 @ X25 @ (k6_relat_1 @ X26)))
% 9.82/10.09          | ~ (v1_relat_1 @ X25))),
% 9.82/10.09      inference('cnf', [status(esa)], [t123_relat_1])).
% 9.82/10.09  thf(t55_relat_1, axiom,
% 9.82/10.09    (![A:$i]:
% 9.82/10.09     ( ( v1_relat_1 @ A ) =>
% 9.82/10.09       ( ![B:$i]:
% 9.82/10.09         ( ( v1_relat_1 @ B ) =>
% 9.82/10.09           ( ![C:$i]:
% 9.82/10.09             ( ( v1_relat_1 @ C ) =>
% 9.82/10.09               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 9.82/10.09                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 9.82/10.09  thf('8', plain,
% 9.82/10.09      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.82/10.09         (~ (v1_relat_1 @ X29)
% 9.82/10.09          | ((k5_relat_1 @ (k5_relat_1 @ X30 @ X29) @ X31)
% 9.82/10.09              = (k5_relat_1 @ X30 @ (k5_relat_1 @ X29 @ X31)))
% 9.82/10.09          | ~ (v1_relat_1 @ X31)
% 9.82/10.09          | ~ (v1_relat_1 @ X30))),
% 9.82/10.09      inference('cnf', [status(esa)], [t55_relat_1])).
% 9.82/10.09  thf('9', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 9.82/10.09            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 9.82/10.09          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 9.82/10.09          | ~ (v1_relat_1 @ X1)
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 9.82/10.09          | ~ (v1_relat_1 @ X0))),
% 9.82/10.09      inference('sup+', [status(thm)], ['7', '8'])).
% 9.82/10.09  thf('10', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('11', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 9.82/10.09            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 9.82/10.09          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 9.82/10.09          | ~ (v1_relat_1 @ X1)
% 9.82/10.09          | ~ (v1_relat_1 @ X0))),
% 9.82/10.09      inference('demod', [status(thm)], ['9', '10'])).
% 9.82/10.09  thf('12', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.09         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 9.82/10.09          | ~ (v1_relat_1 @ X0)
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 9.82/10.09          | ~ (v1_relat_1 @ X0)
% 9.82/10.09          | ((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 9.82/10.09              = (k5_relat_1 @ X0 @ 
% 9.82/10.09                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 9.82/10.09      inference('sup-', [status(thm)], ['6', '11'])).
% 9.82/10.09  thf('13', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('14', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.09         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 9.82/10.09          | ~ (v1_relat_1 @ X0)
% 9.82/10.09          | ~ (v1_relat_1 @ X0)
% 9.82/10.09          | ((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 9.82/10.09              = (k5_relat_1 @ X0 @ 
% 9.82/10.09                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 9.82/10.09      inference('demod', [status(thm)], ['12', '13'])).
% 9.82/10.09  thf('15', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 9.82/10.09            = (k5_relat_1 @ X0 @ 
% 9.82/10.09               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2))))
% 9.82/10.09          | ~ (v1_relat_1 @ X0)
% 9.82/10.09          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 9.82/10.09      inference('simplify', [status(thm)], ['14'])).
% 9.82/10.09  thf('16', plain,
% 9.82/10.09      (![X25 : $i, X26 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X26 @ X25) = (k5_relat_1 @ X25 @ (k6_relat_1 @ X26)))
% 9.82/10.09          | ~ (v1_relat_1 @ X25))),
% 9.82/10.09      inference('cnf', [status(esa)], [t123_relat_1])).
% 9.82/10.09  thf(t71_relat_1, axiom,
% 9.82/10.09    (![A:$i]:
% 9.82/10.09     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 9.82/10.09       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 9.82/10.09  thf('17', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 9.82/10.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.82/10.09  thf('18', plain,
% 9.82/10.09      (![X36 : $i]:
% 9.82/10.09         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X36)) @ X36) = (X36))
% 9.82/10.09          | ~ (v1_relat_1 @ X36))),
% 9.82/10.09      inference('cnf', [status(esa)], [t78_relat_1])).
% 9.82/10.09  thf('19', plain,
% 9.82/10.09      (![X0 : $i]:
% 9.82/10.09         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 9.82/10.09            = (k6_relat_1 @ X0))
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['17', '18'])).
% 9.82/10.09  thf('20', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('21', plain,
% 9.82/10.09      (![X0 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 9.82/10.09           = (k6_relat_1 @ X0))),
% 9.82/10.09      inference('demod', [status(thm)], ['19', '20'])).
% 9.82/10.09  thf('22', plain,
% 9.82/10.09      (![X29 : $i, X30 : $i, X31 : $i]:
% 9.82/10.09         (~ (v1_relat_1 @ X29)
% 9.82/10.09          | ((k5_relat_1 @ (k5_relat_1 @ X30 @ X29) @ X31)
% 9.82/10.09              = (k5_relat_1 @ X30 @ (k5_relat_1 @ X29 @ X31)))
% 9.82/10.09          | ~ (v1_relat_1 @ X31)
% 9.82/10.09          | ~ (v1_relat_1 @ X30))),
% 9.82/10.09      inference('cnf', [status(esa)], [t55_relat_1])).
% 9.82/10.09  thf('23', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 9.82/10.09            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 9.82/10.09               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 9.82/10.09          | ~ (v1_relat_1 @ X1)
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['21', '22'])).
% 9.82/10.09  thf('24', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('25', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('26', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 9.82/10.09            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 9.82/10.09               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 9.82/10.09          | ~ (v1_relat_1 @ X1))),
% 9.82/10.09      inference('demod', [status(thm)], ['23', '24', '25'])).
% 9.82/10.09  thf('27', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 9.82/10.09            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 9.82/10.09               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['16', '26'])).
% 9.82/10.09  thf('28', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('29', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('30', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 9.82/10.09           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 9.82/10.09              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 9.82/10.09      inference('demod', [status(thm)], ['27', '28', '29'])).
% 9.82/10.09  thf(commutativity_k2_tarski, axiom,
% 9.82/10.09    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 9.82/10.09  thf('31', plain,
% 9.82/10.09      (![X14 : $i, X15 : $i]:
% 9.82/10.09         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 9.82/10.09      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.82/10.09  thf(t12_setfam_1, axiom,
% 9.82/10.09    (![A:$i,B:$i]:
% 9.82/10.09     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.82/10.09  thf('32', plain,
% 9.82/10.09      (![X21 : $i, X22 : $i]:
% 9.82/10.09         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 9.82/10.09      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.82/10.09  thf('33', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 9.82/10.09      inference('sup+', [status(thm)], ['31', '32'])).
% 9.82/10.09  thf('34', plain,
% 9.82/10.09      (![X21 : $i, X22 : $i]:
% 9.82/10.09         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 9.82/10.09      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.82/10.09  thf('35', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.82/10.09      inference('sup+', [status(thm)], ['33', '34'])).
% 9.82/10.09  thf(t17_xboole_1, axiom,
% 9.82/10.09    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 9.82/10.09  thf('36', plain,
% 9.82/10.09      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 9.82/10.09      inference('cnf', [status(esa)], [t17_xboole_1])).
% 9.82/10.09  thf('37', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.82/10.09      inference('sup+', [status(thm)], ['35', '36'])).
% 9.82/10.09  thf('38', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 9.82/10.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.82/10.09  thf(t90_relat_1, axiom,
% 9.82/10.09    (![A:$i,B:$i]:
% 9.82/10.09     ( ( v1_relat_1 @ B ) =>
% 9.82/10.09       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 9.82/10.09         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 9.82/10.09  thf('39', plain,
% 9.82/10.09      (![X39 : $i, X40 : $i]:
% 9.82/10.09         (((k1_relat_1 @ (k7_relat_1 @ X39 @ X40))
% 9.82/10.09            = (k3_xboole_0 @ (k1_relat_1 @ X39) @ X40))
% 9.82/10.09          | ~ (v1_relat_1 @ X39))),
% 9.82/10.09      inference('cnf', [status(esa)], [t90_relat_1])).
% 9.82/10.09  thf('40', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 9.82/10.09            = (k3_xboole_0 @ X0 @ X1))
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['38', '39'])).
% 9.82/10.09  thf('41', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('42', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 9.82/10.09           = (k3_xboole_0 @ X0 @ X1))),
% 9.82/10.09      inference('demod', [status(thm)], ['40', '41'])).
% 9.82/10.09  thf('43', plain,
% 9.82/10.09      (![X25 : $i, X26 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X26 @ X25) = (k5_relat_1 @ X25 @ (k6_relat_1 @ X26)))
% 9.82/10.09          | ~ (v1_relat_1 @ X25))),
% 9.82/10.09      inference('cnf', [status(esa)], [t123_relat_1])).
% 9.82/10.09  thf(t94_relat_1, axiom,
% 9.82/10.09    (![A:$i,B:$i]:
% 9.82/10.09     ( ( v1_relat_1 @ B ) =>
% 9.82/10.09       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 9.82/10.09  thf('44', plain,
% 9.82/10.09      (![X41 : $i, X42 : $i]:
% 9.82/10.09         (((k7_relat_1 @ X42 @ X41) = (k5_relat_1 @ (k6_relat_1 @ X41) @ X42))
% 9.82/10.09          | ~ (v1_relat_1 @ X42))),
% 9.82/10.09      inference('cnf', [status(esa)], [t94_relat_1])).
% 9.82/10.09  thf('45', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 9.82/10.09            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['43', '44'])).
% 9.82/10.09  thf('46', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('47', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('48', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 9.82/10.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('demod', [status(thm)], ['45', '46', '47'])).
% 9.82/10.09  thf('49', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 9.82/10.09           = (k3_xboole_0 @ X0 @ X1))),
% 9.82/10.09      inference('demod', [status(thm)], ['42', '48'])).
% 9.82/10.09  thf(t77_relat_1, axiom,
% 9.82/10.09    (![A:$i,B:$i]:
% 9.82/10.09     ( ( v1_relat_1 @ B ) =>
% 9.82/10.09       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 9.82/10.09         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 9.82/10.09  thf('50', plain,
% 9.82/10.09      (![X34 : $i, X35 : $i]:
% 9.82/10.09         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 9.82/10.09          | ((k5_relat_1 @ (k6_relat_1 @ X35) @ X34) = (X34))
% 9.82/10.09          | ~ (v1_relat_1 @ X34))),
% 9.82/10.09      inference('cnf', [status(esa)], [t77_relat_1])).
% 9.82/10.09  thf('51', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.09         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 9.82/10.09          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.82/10.09          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 9.82/10.09              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.82/10.09              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 9.82/10.09      inference('sup-', [status(thm)], ['49', '50'])).
% 9.82/10.09  thf('52', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 9.82/10.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.82/10.09  thf(t124_relat_1, axiom,
% 9.82/10.09    (![A:$i,B:$i]:
% 9.82/10.09     ( ( v1_relat_1 @ B ) =>
% 9.82/10.09       ( ( k8_relat_1 @ A @ B ) =
% 9.82/10.09         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 9.82/10.09  thf('53', plain,
% 9.82/10.09      (![X27 : $i, X28 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X28 @ X27)
% 9.82/10.09            = (k3_xboole_0 @ X27 @ (k2_zfmisc_1 @ (k1_relat_1 @ X27) @ X28)))
% 9.82/10.09          | ~ (v1_relat_1 @ X27))),
% 9.82/10.09      inference('cnf', [status(esa)], [t124_relat_1])).
% 9.82/10.09  thf('54', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 9.82/10.09            = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['52', '53'])).
% 9.82/10.09  thf('55', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('56', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 9.82/10.09           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 9.82/10.09      inference('demod', [status(thm)], ['54', '55'])).
% 9.82/10.09  thf(fc1_relat_1, axiom,
% 9.82/10.09    (![A:$i,B:$i]:
% 9.82/10.09     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.82/10.09  thf('57', plain,
% 9.82/10.09      (![X23 : $i, X24 : $i]:
% 9.82/10.09         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k3_xboole_0 @ X23 @ X24)))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc1_relat_1])).
% 9.82/10.09  thf('58', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['56', '57'])).
% 9.82/10.09  thf('59', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('60', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('demod', [status(thm)], ['58', '59'])).
% 9.82/10.09  thf('61', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.09         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 9.82/10.09          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 9.82/10.09              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.82/10.09              = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 9.82/10.09      inference('demod', [status(thm)], ['51', '60'])).
% 9.82/10.09  thf('62', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 9.82/10.09           (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.82/10.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('sup-', [status(thm)], ['37', '61'])).
% 9.82/10.09  thf('63', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 9.82/10.09           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['30', '62'])).
% 9.82/10.09  thf('64', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 9.82/10.09            = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))
% 9.82/10.09          | ~ (v1_relat_1 @ X0)
% 9.82/10.09          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 9.82/10.09      inference('demod', [status(thm)], ['15', '63'])).
% 9.82/10.09  thf('65', plain,
% 9.82/10.09      (![X27 : $i, X28 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X28 @ X27)
% 9.82/10.09            = (k3_xboole_0 @ X27 @ (k2_zfmisc_1 @ (k1_relat_1 @ X27) @ X28)))
% 9.82/10.09          | ~ (v1_relat_1 @ X27))),
% 9.82/10.09      inference('cnf', [status(esa)], [t124_relat_1])).
% 9.82/10.09  thf('66', plain,
% 9.82/10.09      (![X23 : $i, X24 : $i]:
% 9.82/10.09         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k3_xboole_0 @ X23 @ X24)))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc1_relat_1])).
% 9.82/10.09  thf('67', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 9.82/10.09          | ~ (v1_relat_1 @ X0)
% 9.82/10.09          | ~ (v1_relat_1 @ X0))),
% 9.82/10.09      inference('sup+', [status(thm)], ['65', '66'])).
% 9.82/10.09  thf('68', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 9.82/10.09      inference('simplify', [status(thm)], ['67'])).
% 9.82/10.09  thf('69', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.09         (~ (v1_relat_1 @ X0)
% 9.82/10.09          | ((k8_relat_1 @ X2 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 9.82/10.09              = (k5_relat_1 @ X0 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)))))),
% 9.82/10.09      inference('clc', [status(thm)], ['64', '68'])).
% 9.82/10.09  thf('70', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (((k8_relat_1 @ X1 @ 
% 9.82/10.09            (k5_relat_1 @ 
% 9.82/10.09             (k6_relat_1 @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 9.82/10.09             (k6_relat_1 @ X0)))
% 9.82/10.09            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.82/10.09          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 9.82/10.09          | ~ (v1_relat_1 @ 
% 9.82/10.09               (k6_relat_1 @ 
% 9.82/10.09                (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))))),
% 9.82/10.09      inference('sup+', [status(thm)], ['5', '69'])).
% 9.82/10.09  thf('71', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 9.82/10.09           = (k3_xboole_0 @ X0 @ X1))),
% 9.82/10.09      inference('demod', [status(thm)], ['42', '48'])).
% 9.82/10.09  thf('72', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 9.82/10.09           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['30', '62'])).
% 9.82/10.09  thf('73', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.82/10.09      inference('sup+', [status(thm)], ['35', '36'])).
% 9.82/10.09  thf('74', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 9.82/10.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.82/10.09  thf(t79_relat_1, axiom,
% 9.82/10.09    (![A:$i,B:$i]:
% 9.82/10.09     ( ( v1_relat_1 @ B ) =>
% 9.82/10.09       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 9.82/10.09         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 9.82/10.09  thf('75', plain,
% 9.82/10.09      (![X37 : $i, X38 : $i]:
% 9.82/10.09         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 9.82/10.09          | ((k5_relat_1 @ X37 @ (k6_relat_1 @ X38)) = (X37))
% 9.82/10.09          | ~ (v1_relat_1 @ X37))),
% 9.82/10.09      inference('cnf', [status(esa)], [t79_relat_1])).
% 9.82/10.09  thf('76', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (~ (r1_tarski @ X0 @ X1)
% 9.82/10.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 9.82/10.09          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 9.82/10.09              = (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('sup-', [status(thm)], ['74', '75'])).
% 9.82/10.09  thf('77', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('78', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (~ (r1_tarski @ X0 @ X1)
% 9.82/10.09          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 9.82/10.09              = (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('demod', [status(thm)], ['76', '77'])).
% 9.82/10.09  thf('79', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.82/10.09           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.82/10.09      inference('sup-', [status(thm)], ['73', '78'])).
% 9.82/10.09  thf('80', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 9.82/10.09           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['30', '62'])).
% 9.82/10.09  thf('81', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 9.82/10.09           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.82/10.09      inference('demod', [status(thm)], ['79', '80'])).
% 9.82/10.09  thf('82', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.82/10.09      inference('sup+', [status(thm)], ['33', '34'])).
% 9.82/10.09  thf('83', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.82/10.09           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.82/10.09      inference('sup-', [status(thm)], ['73', '78'])).
% 9.82/10.09  thf('84', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.82/10.09           (k6_relat_1 @ X1)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['82', '83'])).
% 9.82/10.09  thf('85', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 9.82/10.09           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['30', '62'])).
% 9.82/10.09  thf('86', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 9.82/10.09           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.82/10.09      inference('demod', [status(thm)], ['84', '85'])).
% 9.82/10.09  thf('87', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('demod', [status(thm)], ['58', '59'])).
% 9.82/10.09  thf('88', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 9.82/10.09           = (k3_xboole_0 @ X0 @ X1))),
% 9.82/10.09      inference('demod', [status(thm)], ['42', '48'])).
% 9.82/10.09  thf('89', plain, (![X43 : $i]: (v1_relat_1 @ (k6_relat_1 @ X43))),
% 9.82/10.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.82/10.09  thf('90', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 9.82/10.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('demod', [status(thm)],
% 9.82/10.09                ['70', '71', '72', '81', '86', '87', '88', '89'])).
% 9.82/10.09  thf('91', plain,
% 9.82/10.09      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 9.82/10.09         != (k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 9.82/10.09      inference('demod', [status(thm)], ['4', '90'])).
% 9.82/10.09  thf('92', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.82/10.09      inference('sup+', [status(thm)], ['33', '34'])).
% 9.82/10.09  thf('93', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 9.82/10.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('demod', [status(thm)],
% 9.82/10.09                ['70', '71', '72', '81', '86', '87', '88', '89'])).
% 9.82/10.09  thf('94', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 9.82/10.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['92', '93'])).
% 9.82/10.09  thf('95', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 9.82/10.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 9.82/10.09      inference('demod', [status(thm)],
% 9.82/10.09                ['70', '71', '72', '81', '86', '87', '88', '89'])).
% 9.82/10.09  thf('96', plain,
% 9.82/10.09      (![X0 : $i, X1 : $i]:
% 9.82/10.09         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 9.82/10.09           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 9.82/10.09      inference('sup+', [status(thm)], ['94', '95'])).
% 9.82/10.09  thf('97', plain,
% 9.82/10.09      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 9.82/10.09         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 9.82/10.09      inference('demod', [status(thm)], ['91', '96'])).
% 9.82/10.09  thf('98', plain, ($false), inference('simplify', [status(thm)], ['97'])).
% 9.82/10.09  
% 9.82/10.09  % SZS output end Refutation
% 9.82/10.09  
% 9.94/10.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
