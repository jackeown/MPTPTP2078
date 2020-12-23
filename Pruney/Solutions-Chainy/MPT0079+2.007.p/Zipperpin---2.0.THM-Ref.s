%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RDoJ5w9YH1

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:57 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 928 expanded)
%              Number of leaves         :   30 ( 321 expanded)
%              Depth                    :   26
%              Number of atoms          : 1045 (6955 expanded)
%              Number of equality atoms :  128 ( 851 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('12',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_xboole_0 @ X31 )
      | ~ ( v1_xboole_0 @ X32 )
      | ( X31 = X32 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X21 ) @ X20 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['17','28'])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k2_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('36',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X21 ) @ X20 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('48',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
    = sk_B_1 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('53',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B_1 )
    = sk_D ),
    inference('sup+',[status(thm)],['51','67'])).

thf('69',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46','68'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('71',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('74',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('77',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k2_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ X0 )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k2_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('86',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('89',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('91',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('93',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('97',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['86','97'])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['29','98'])).

thf('100',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = ( k3_xboole_0 @ sk_D @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = ( k3_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46','68'])).

thf('105',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('107',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_C_1 ) )
    = sk_D ),
    inference('sup+',[status(thm)],['105','108'])).

thf('110',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['29','98'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('112',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','112'])).

thf('114',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('115',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('118',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_A )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('120',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['93','94'])).

thf('121',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('123',plain,(
    sk_C_1 = sk_B_1 ),
    inference(demod,[status(thm)],['115','121','122'])).

thf('124',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['123','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RDoJ5w9YH1
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.83  % Solved by: fo/fo7.sh
% 0.62/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.83  % done 824 iterations in 0.368s
% 0.62/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.83  % SZS output start Refutation
% 0.62/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.62/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.62/0.83  thf(sk_D_type, type, sk_D: $i).
% 0.62/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.62/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.62/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.62/0.83  thf(t72_xboole_1, conjecture,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.83     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.62/0.83         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.62/0.83       ( ( C ) = ( B ) ) ))).
% 0.62/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.83        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.62/0.83            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.62/0.83          ( ( C ) = ( B ) ) ) )),
% 0.62/0.83    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.62/0.83  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf(t4_xboole_0, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.62/0.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.62/0.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.62/0.83            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.62/0.83  thf('1', plain,
% 0.62/0.83      (![X7 : $i, X8 : $i]:
% 0.62/0.83         ((r1_xboole_0 @ X7 @ X8)
% 0.62/0.83          | (r2_hidden @ (sk_C @ X8 @ X7) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.62/0.83  thf(commutativity_k3_xboole_0, axiom,
% 0.62/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.62/0.83  thf('2', plain,
% 0.62/0.83      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.83  thf('3', plain,
% 0.62/0.83      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.62/0.83         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.62/0.83          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.62/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.62/0.83  thf('4', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.62/0.83          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.62/0.83  thf('5', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('sup-', [status(thm)], ['1', '4'])).
% 0.62/0.83  thf('6', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.62/0.83      inference('sup-', [status(thm)], ['0', '5'])).
% 0.62/0.83  thf(d1_xboole_0, axiom,
% 0.62/0.83    (![A:$i]:
% 0.62/0.83     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.83  thf('7', plain,
% 0.62/0.83      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.62/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.83  thf('8', plain,
% 0.62/0.83      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.62/0.83         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.62/0.83          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.62/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.62/0.83  thf('9', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.83  thf('10', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_D))),
% 0.62/0.83      inference('sup-', [status(thm)], ['6', '9'])).
% 0.62/0.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.62/0.83  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.62/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.62/0.83  thf(t8_boole, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.62/0.83  thf('12', plain,
% 0.62/0.83      (![X31 : $i, X32 : $i]:
% 0.62/0.83         (~ (v1_xboole_0 @ X31) | ~ (v1_xboole_0 @ X32) | ((X31) = (X32)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t8_boole])).
% 0.62/0.83  thf('13', plain,
% 0.62/0.83      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['11', '12'])).
% 0.62/0.83  thf('14', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ sk_D))),
% 0.62/0.83      inference('sup-', [status(thm)], ['10', '13'])).
% 0.62/0.83  thf('15', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf(commutativity_k2_xboole_0, axiom,
% 0.62/0.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.62/0.83  thf('16', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.83  thf('17', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.62/0.83      inference('demod', [status(thm)], ['15', '16'])).
% 0.62/0.83  thf(t3_boole, axiom,
% 0.62/0.83    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.62/0.83  thf('18', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.62/0.83      inference('cnf', [status(esa)], [t3_boole])).
% 0.62/0.83  thf(t48_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.62/0.83  thf('19', plain,
% 0.62/0.83      (![X22 : $i, X23 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.62/0.83           = (k3_xboole_0 @ X22 @ X23))),
% 0.62/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.83  thf('20', plain,
% 0.62/0.83      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['18', '19'])).
% 0.62/0.83  thf(t2_boole, axiom,
% 0.62/0.83    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.62/0.83  thf('21', plain,
% 0.62/0.83      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.62/0.83      inference('cnf', [status(esa)], [t2_boole])).
% 0.62/0.83  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.83      inference('demod', [status(thm)], ['20', '21'])).
% 0.62/0.83  thf(t42_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.62/0.83       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.62/0.83  thf('23', plain,
% 0.62/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X21) @ X20)
% 0.62/0.83           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.62/0.83              (k4_xboole_0 @ X21 @ X20)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.62/0.83  thf('24', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.62/0.83           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['22', '23'])).
% 0.62/0.83  thf('25', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.83  thf(t1_boole, axiom,
% 0.62/0.83    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.62/0.83  thf('26', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.62/0.83      inference('cnf', [status(esa)], [t1_boole])).
% 0.62/0.83  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('28', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.62/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['24', '27'])).
% 0.62/0.83  thf('29', plain,
% 0.62/0.83      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.62/0.83         = (k4_xboole_0 @ sk_D @ sk_C_1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['17', '28'])).
% 0.62/0.83  thf('30', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.62/0.83      inference('demod', [status(thm)], ['15', '16'])).
% 0.62/0.83  thf('31', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.83  thf(t6_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.62/0.83  thf('32', plain,
% 0.62/0.83      (![X29 : $i, X30 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ X29 @ (k2_xboole_0 @ X29 @ X30))
% 0.62/0.83           = (k2_xboole_0 @ X29 @ X30))),
% 0.62/0.83      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.62/0.83  thf('33', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.62/0.83           = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['31', '32'])).
% 0.62/0.83  thf('34', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.62/0.83         = (k2_xboole_0 @ sk_D @ sk_C_1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['30', '33'])).
% 0.62/0.83  thf('35', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.83  thf('36', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.62/0.83      inference('demod', [status(thm)], ['15', '16'])).
% 0.62/0.83  thf('37', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.62/0.83         = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.62/0.83  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.83      inference('demod', [status(thm)], ['20', '21'])).
% 0.62/0.83  thf('39', plain,
% 0.62/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X21) @ X20)
% 0.62/0.83           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.62/0.83              (k4_xboole_0 @ X21 @ X20)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.62/0.83  thf('40', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.62/0.83           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['38', '39'])).
% 0.62/0.83  thf('41', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.83  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('43', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.62/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.62/0.83  thf('44', plain,
% 0.62/0.83      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ 
% 0.62/0.83         (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.62/0.83         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['37', '43'])).
% 0.62/0.83  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.83      inference('demod', [status(thm)], ['20', '21'])).
% 0.62/0.83  thf(t41_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.62/0.83       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.62/0.83  thf('46', plain,
% 0.62/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.62/0.83           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.62/0.83  thf('47', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ sk_D))),
% 0.62/0.83      inference('sup-', [status(thm)], ['10', '13'])).
% 0.62/0.83  thf(t51_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.62/0.83       ( A ) ))).
% 0.62/0.83  thf('48', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.62/0.83           = (X27))),
% 0.62/0.83      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.62/0.83  thf('49', plain,
% 0.62/0.83      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_D)) = (sk_B_1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['47', '48'])).
% 0.62/0.83  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('51', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1))),
% 0.62/0.83      inference('demod', [status(thm)], ['49', '50'])).
% 0.62/0.83  thf('52', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.62/0.83      inference('cnf', [status(esa)], [t1_boole])).
% 0.62/0.83  thf('53', plain,
% 0.62/0.83      (![X29 : $i, X30 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ X29 @ (k2_xboole_0 @ X29 @ X30))
% 0.62/0.83           = (k2_xboole_0 @ X29 @ X30))),
% 0.62/0.83      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.62/0.83  thf('54', plain,
% 0.62/0.83      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['52', '53'])).
% 0.62/0.83  thf('55', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.62/0.83      inference('cnf', [status(esa)], [t1_boole])).
% 0.62/0.83  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['54', '55'])).
% 0.62/0.83  thf('57', plain,
% 0.62/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.62/0.83           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.62/0.83  thf('58', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.62/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['56', '57'])).
% 0.62/0.83  thf('59', plain,
% 0.62/0.83      (![X22 : $i, X23 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.62/0.83           = (k3_xboole_0 @ X22 @ X23))),
% 0.62/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.83  thf('60', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.62/0.83           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['58', '59'])).
% 0.62/0.83  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.83      inference('demod', [status(thm)], ['20', '21'])).
% 0.62/0.83  thf('62', plain,
% 0.62/0.83      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.83  thf('63', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.62/0.83  thf('64', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.62/0.83           = (X27))),
% 0.62/0.83      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.62/0.83  thf('65', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ k1_xboole_0 @ 
% 0.62/0.83           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['63', '64'])).
% 0.62/0.83  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('67', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['65', '66'])).
% 0.62/0.83  thf('68', plain, (((k4_xboole_0 @ sk_D @ sk_B_1) = (sk_D))),
% 0.62/0.83      inference('sup+', [status(thm)], ['51', '67'])).
% 0.62/0.83  thf('69', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['44', '45', '46', '68'])).
% 0.62/0.83  thf(t39_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.62/0.83  thf('70', plain,
% 0.62/0.83      (![X13 : $i, X14 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.62/0.83           = (k2_xboole_0 @ X13 @ X14))),
% 0.62/0.83      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.62/0.83  thf('71', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.62/0.83      inference('sup+', [status(thm)], ['69', '70'])).
% 0.62/0.83  thf('72', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.83  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('74', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.62/0.83      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.62/0.83  thf('75', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.83  thf('76', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.62/0.83      inference('demod', [status(thm)], ['15', '16'])).
% 0.62/0.83  thf(t4_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.62/0.83       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.62/0.83  thf('77', plain,
% 0.62/0.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X26)
% 0.62/0.83           = (k2_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X26)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.62/0.83  thf('78', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ X0)
% 0.62/0.83           = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['76', '77'])).
% 0.62/0.83  thf('79', plain,
% 0.62/0.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X26)
% 0.62/0.83           = (k2_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X26)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.62/0.83  thf('80', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ X0))
% 0.62/0.83           = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_D @ X0)))),
% 0.62/0.83      inference('demod', [status(thm)], ['78', '79'])).
% 0.62/0.83  thf('81', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ X0))
% 0.62/0.83           = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_D)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['75', '80'])).
% 0.62/0.83  thf('82', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ sk_A))
% 0.62/0.83         = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.62/0.83      inference('sup+', [status(thm)], ['74', '81'])).
% 0.62/0.83  thf('83', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['54', '55'])).
% 0.62/0.83  thf('84', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['82', '83'])).
% 0.62/0.83  thf('85', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.62/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['24', '27'])).
% 0.62/0.83  thf('86', plain,
% 0.62/0.83      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.62/0.83         = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['84', '85'])).
% 0.62/0.83  thf('87', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('88', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.83  thf('89', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.62/0.83      inference('sup-', [status(thm)], ['87', '88'])).
% 0.62/0.83  thf('90', plain,
% 0.62/0.83      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.62/0.83      inference('sup-', [status(thm)], ['11', '12'])).
% 0.62/0.83  thf('91', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.62/0.83      inference('sup-', [status(thm)], ['89', '90'])).
% 0.62/0.83  thf('92', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.62/0.83           = (X27))),
% 0.62/0.83      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.62/0.83  thf('93', plain,
% 0.62/0.83      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A)) = (sk_C_1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['91', '92'])).
% 0.62/0.83  thf('94', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('95', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.62/0.83      inference('demod', [status(thm)], ['93', '94'])).
% 0.62/0.83  thf('96', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['65', '66'])).
% 0.62/0.83  thf('97', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.62/0.83      inference('sup+', [status(thm)], ['95', '96'])).
% 0.62/0.83  thf('98', plain,
% 0.62/0.83      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_C_1) = (sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['86', '97'])).
% 0.62/0.83  thf('99', plain, (((k4_xboole_0 @ sk_D @ sk_C_1) = (sk_A))),
% 0.62/0.83      inference('sup+', [status(thm)], ['29', '98'])).
% 0.62/0.83  thf('100', plain,
% 0.62/0.83      (![X22 : $i, X23 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.62/0.83           = (k3_xboole_0 @ X22 @ X23))),
% 0.62/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.83  thf('101', plain,
% 0.62/0.83      (((k4_xboole_0 @ sk_D @ sk_A) = (k3_xboole_0 @ sk_D @ sk_C_1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['99', '100'])).
% 0.62/0.83  thf('102', plain,
% 0.62/0.83      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.83  thf('103', plain,
% 0.62/0.83      (((k4_xboole_0 @ sk_D @ sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_D))),
% 0.62/0.83      inference('demod', [status(thm)], ['101', '102'])).
% 0.62/0.83  thf('104', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['44', '45', '46', '68'])).
% 0.62/0.83  thf('105', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_D))),
% 0.62/0.83      inference('sup+', [status(thm)], ['103', '104'])).
% 0.62/0.83  thf('106', plain,
% 0.62/0.83      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.62/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.83  thf('107', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.62/0.83           = (X27))),
% 0.62/0.83      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.62/0.83  thf('108', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.62/0.83           = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['106', '107'])).
% 0.62/0.83  thf('109', plain,
% 0.62/0.83      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_C_1)) = (sk_D))),
% 0.62/0.83      inference('sup+', [status(thm)], ['105', '108'])).
% 0.62/0.83  thf('110', plain, (((k4_xboole_0 @ sk_D @ sk_C_1) = (sk_A))),
% 0.62/0.83      inference('sup+', [status(thm)], ['29', '98'])).
% 0.62/0.83  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('112', plain, (((sk_A) = (sk_D))),
% 0.62/0.83      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.62/0.83  thf('113', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['14', '112'])).
% 0.62/0.83  thf('114', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i]:
% 0.62/0.83         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.62/0.83           = (X27))),
% 0.62/0.83      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.62/0.83  thf('115', plain,
% 0.62/0.83      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_A)) = (sk_B_1))),
% 0.62/0.83      inference('sup+', [status(thm)], ['113', '114'])).
% 0.62/0.83  thf('116', plain,
% 0.62/0.83      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['82', '83'])).
% 0.62/0.83  thf('117', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.62/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.62/0.83  thf('118', plain,
% 0.62/0.83      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_A)
% 0.62/0.83         = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.62/0.83      inference('sup+', [status(thm)], ['116', '117'])).
% 0.62/0.83  thf('119', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.62/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.62/0.83  thf('120', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.62/0.83      inference('demod', [status(thm)], ['93', '94'])).
% 0.62/0.83  thf('121', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.62/0.83      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.62/0.83  thf('122', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('123', plain, (((sk_C_1) = (sk_B_1))),
% 0.62/0.83      inference('demod', [status(thm)], ['115', '121', '122'])).
% 0.62/0.83  thf('124', plain, (((sk_C_1) != (sk_B_1))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('125', plain, ($false),
% 0.62/0.83      inference('simplify_reflect-', [status(thm)], ['123', '124'])).
% 0.62/0.83  
% 0.62/0.83  % SZS output end Refutation
% 0.62/0.83  
% 0.62/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
