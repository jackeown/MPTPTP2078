%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b8KmS4PCtJ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:53 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 151 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  591 (1038 expanded)
%              Number of equality atoms :   73 ( 131 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( v1_xboole_0 @ X27 )
      | ( X26 = X27 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X21 ) @ X20 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('28',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('30',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','51'])).

thf('53',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['41','52'])).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('57',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['39','40','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('60',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X21 ) @ X20 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['58','64'])).

thf('66',plain,(
    sk_A = sk_C_1 ),
    inference('sup+',[status(thm)],['14','65'])).

thf('67',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b8KmS4PCtJ
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:11:46 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 559 iterations in 0.196s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(t71_xboole_1, conjecture,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.47/0.64         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.47/0.64       ( ( A ) = ( C ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.64        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.47/0.64            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.47/0.64          ( ( A ) = ( C ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.47/0.64  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(d1_xboole_0, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.47/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.64  thf(t4_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.47/0.64          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.47/0.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.64  thf('4', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '3'])).
% 0.47/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.64  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf(t8_boole, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (![X26 : $i, X27 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ X26) | ~ (v1_xboole_0 @ X27) | ((X26) = (X27)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t8_boole])).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.64  thf('8', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['4', '7'])).
% 0.47/0.64  thf(t51_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.47/0.64       ( A ) ))).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (![X24 : $i, X25 : $i]:
% 0.47/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.47/0.64           = (X24))),
% 0.47/0.64      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.47/0.64      inference('sup+', [status(thm)], ['8', '9'])).
% 0.47/0.64  thf(commutativity_k2_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.64  thf(t1_boole, axiom,
% 0.47/0.64    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.64  thf('12', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.47/0.64      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.64  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('14', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['10', '13'])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t3_boole, axiom,
% 0.47/0.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.64  thf('16', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.64  thf(t48_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (![X22 : $i, X23 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.47/0.64           = (k3_xboole_0 @ X22 @ X23))),
% 0.47/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.47/0.64  thf(t2_boole, axiom,
% 0.47/0.64    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.64  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.64  thf(t42_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.64       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X21) @ X20)
% 0.47/0.64           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.47/0.64              (k4_xboole_0 @ X21 @ X20)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.47/0.64           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.47/0.64  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.47/0.64           = (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1)
% 0.47/0.64         = (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['15', '24'])).
% 0.47/0.64  thf('26', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.64  thf('28', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.64  thf('30', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      (![X24 : $i, X25 : $i]:
% 0.47/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.47/0.64           = (X24))),
% 0.47/0.64      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.47/0.64           = (X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['31', '32'])).
% 0.47/0.64  thf('34', plain,
% 0.47/0.64      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.47/0.64         = (sk_B_1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['30', '33'])).
% 0.47/0.64  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('36', plain, (((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.47/0.64  thf('37', plain,
% 0.47/0.64      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1) = (sk_B_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['25', '36'])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X22 : $i, X23 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.47/0.64           = (k3_xboole_0 @ X22 @ X23))),
% 0.47/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.47/0.64         = (k3_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['37', '38'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.64  thf(t41_xboole_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.64       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.47/0.64           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.47/0.64  thf('44', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.64           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['42', '43'])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.47/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['45', '46'])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      (![X24 : $i, X25 : $i]:
% 0.47/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 0.47/0.64           = (X24))),
% 0.47/0.64      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.47/0.64           = (k1_xboole_0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['47', '48'])).
% 0.47/0.64  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['49', '50'])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['44', '51'])).
% 0.47/0.64  thf('53', plain,
% 0.47/0.64      (((k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['41', '52'])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      (![X22 : $i, X23 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.47/0.64           = (k3_xboole_0 @ X22 @ X23))),
% 0.47/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 0.47/0.64         = (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['53', '54'])).
% 0.47/0.64  thf('56', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_boole])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B_1)))),
% 0.47/0.64      inference('demod', [status(thm)], ['55', '56'])).
% 0.47/0.64  thf('58', plain,
% 0.47/0.64      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1) = (sk_C_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['39', '40', '57'])).
% 0.47/0.64  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X21) @ X20)
% 0.47/0.64           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.47/0.64              (k4_xboole_0 @ X21 @ X20)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.47/0.64           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['59', '60'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.47/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.47/0.64  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.64  thf('64', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.47/0.64           = (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.47/0.64  thf('65', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_C_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['58', '64'])).
% 0.47/0.64  thf('66', plain, (((sk_A) = (sk_C_1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['14', '65'])).
% 0.47/0.64  thf('67', plain, (((sk_A) != (sk_C_1))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('68', plain, ($false),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
