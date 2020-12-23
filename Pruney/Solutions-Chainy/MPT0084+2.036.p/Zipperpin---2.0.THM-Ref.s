%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XKN3YwJsSS

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:23 EST 2020

% Result     : Theorem 6.85s
% Output     : Refutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 163 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   21
%              Number of atoms          :  633 (1109 expanded)
%              Number of equality atoms :   27 (  61 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r1_xboole_0 @ X44 @ X45 )
      | ( r1_xboole_0 @ X44 @ ( k3_xboole_0 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('7',plain,(
    ! [X41: $i] :
      ( r1_xboole_0 @ X41 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X35 @ X36 ) @ ( k3_xboole_0 @ X35 @ X37 ) ) @ ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X34: $i] :
      ( r1_tarski @ k1_xboole_0 @ X34 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['11','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['11','14','15'])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X31 @ X32 ) @ ( k2_xboole_0 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) @ ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t26_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r1_tarski @ ( k3_xboole_0 @ X26 @ X28 ) @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t26_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ X23 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C_2 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C_2 )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('58',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('60',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('65',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XKN3YwJsSS
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.85/7.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.85/7.03  % Solved by: fo/fo7.sh
% 6.85/7.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.85/7.03  % done 15909 iterations in 6.572s
% 6.85/7.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.85/7.03  % SZS output start Refutation
% 6.85/7.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.85/7.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.85/7.03  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.85/7.03  thf(sk_A_type, type, sk_A: $i).
% 6.85/7.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.85/7.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.85/7.03  thf(sk_C_2_type, type, sk_C_2: $i).
% 6.85/7.03  thf(sk_B_type, type, sk_B: $i).
% 6.85/7.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.85/7.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.85/7.03  thf(t77_xboole_1, conjecture,
% 6.85/7.03    (![A:$i,B:$i,C:$i]:
% 6.85/7.03     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 6.85/7.03          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 6.85/7.03  thf(zf_stmt_0, negated_conjecture,
% 6.85/7.03    (~( ![A:$i,B:$i,C:$i]:
% 6.85/7.03        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 6.85/7.04             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 6.85/7.04    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 6.85/7.04  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 6.85/7.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.04  thf(t4_xboole_0, axiom,
% 6.85/7.04    (![A:$i,B:$i]:
% 6.85/7.04     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 6.85/7.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 6.85/7.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 6.85/7.04            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 6.85/7.04  thf('1', plain,
% 6.85/7.04      (![X12 : $i, X13 : $i]:
% 6.85/7.04         ((r1_xboole_0 @ X12 @ X13)
% 6.85/7.04          | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 6.85/7.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 6.85/7.04  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_2))),
% 6.85/7.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.04  thf(t74_xboole_1, axiom,
% 6.85/7.04    (![A:$i,B:$i,C:$i]:
% 6.85/7.04     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 6.85/7.04          ( r1_xboole_0 @ A @ B ) ) ))).
% 6.85/7.04  thf('3', plain,
% 6.85/7.04      (![X44 : $i, X45 : $i, X46 : $i]:
% 6.85/7.04         (~ (r1_xboole_0 @ X44 @ X45)
% 6.85/7.04          | (r1_xboole_0 @ X44 @ (k3_xboole_0 @ X45 @ X46)))),
% 6.85/7.04      inference('cnf', [status(esa)], [t74_xboole_1])).
% 6.85/7.04  thf('4', plain,
% 6.85/7.04      (![X0 : $i]:
% 6.85/7.04         (r1_xboole_0 @ sk_A @ 
% 6.85/7.04          (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_2) @ X0))),
% 6.85/7.04      inference('sup-', [status(thm)], ['2', '3'])).
% 6.85/7.04  thf(symmetry_r1_xboole_0, axiom,
% 6.85/7.04    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 6.85/7.04  thf('5', plain,
% 6.85/7.04      (![X6 : $i, X7 : $i]:
% 6.85/7.04         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 6.85/7.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 6.85/7.04  thf('6', plain,
% 6.85/7.04      (![X0 : $i]:
% 6.85/7.04         (r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_2) @ X0) @ 
% 6.85/7.04          sk_A)),
% 6.85/7.04      inference('sup-', [status(thm)], ['4', '5'])).
% 6.85/7.04  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 6.85/7.04  thf('7', plain, (![X41 : $i]: (r1_xboole_0 @ X41 @ k1_xboole_0)),
% 6.85/7.04      inference('cnf', [status(esa)], [t65_xboole_1])).
% 6.85/7.04  thf(d7_xboole_0, axiom,
% 6.85/7.04    (![A:$i,B:$i]:
% 6.85/7.04     ( ( r1_xboole_0 @ A @ B ) <=>
% 6.85/7.04       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 6.85/7.04  thf('8', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i]:
% 6.85/7.04         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 6.85/7.04      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.85/7.04  thf('9', plain,
% 6.85/7.04      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.85/7.04      inference('sup-', [status(thm)], ['7', '8'])).
% 6.85/7.04  thf(t31_xboole_1, axiom,
% 6.85/7.04    (![A:$i,B:$i,C:$i]:
% 6.85/7.04     ( r1_tarski @
% 6.85/7.04       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 6.85/7.04       ( k2_xboole_0 @ B @ C ) ))).
% 6.85/7.04  thf('10', plain,
% 6.85/7.04      (![X35 : $i, X36 : $i, X37 : $i]:
% 6.85/7.04         (r1_tarski @ 
% 6.85/7.04          (k2_xboole_0 @ (k3_xboole_0 @ X35 @ X36) @ (k3_xboole_0 @ X35 @ X37)) @ 
% 6.85/7.04          (k2_xboole_0 @ X36 @ X37))),
% 6.85/7.04      inference('cnf', [status(esa)], [t31_xboole_1])).
% 6.85/7.04  thf('11', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i]:
% 6.85/7.04         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 6.85/7.04          (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 6.85/7.04      inference('sup+', [status(thm)], ['9', '10'])).
% 6.85/7.04  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.85/7.04  thf('12', plain, (![X34 : $i]: (r1_tarski @ k1_xboole_0 @ X34)),
% 6.85/7.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.85/7.04  thf(t12_xboole_1, axiom,
% 6.85/7.04    (![A:$i,B:$i]:
% 6.85/7.04     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.85/7.04  thf('13', plain,
% 6.85/7.04      (![X19 : $i, X20 : $i]:
% 6.85/7.04         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 6.85/7.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.85/7.04  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.85/7.04      inference('sup-', [status(thm)], ['12', '13'])).
% 6.85/7.04  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.85/7.04      inference('sup-', [status(thm)], ['12', '13'])).
% 6.85/7.04  thf('16', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.85/7.04      inference('demod', [status(thm)], ['11', '14', '15'])).
% 6.85/7.04  thf('17', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.85/7.04      inference('demod', [status(thm)], ['11', '14', '15'])).
% 6.85/7.04  thf('18', plain,
% 6.85/7.04      (![X19 : $i, X20 : $i]:
% 6.85/7.04         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 6.85/7.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.85/7.04  thf('19', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i]:
% 6.85/7.04         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 6.85/7.04      inference('sup-', [status(thm)], ['17', '18'])).
% 6.85/7.04  thf(t11_xboole_1, axiom,
% 6.85/7.04    (![A:$i,B:$i,C:$i]:
% 6.85/7.04     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 6.85/7.04  thf('20', plain,
% 6.85/7.04      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.85/7.04         ((r1_tarski @ X16 @ X17)
% 6.85/7.04          | ~ (r1_tarski @ (k2_xboole_0 @ X16 @ X18) @ X17))),
% 6.85/7.04      inference('cnf', [status(esa)], [t11_xboole_1])).
% 6.85/7.04  thf('21', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.04         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 6.85/7.04      inference('sup-', [status(thm)], ['19', '20'])).
% 6.85/7.04  thf('22', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.04         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 6.85/7.04      inference('sup-', [status(thm)], ['16', '21'])).
% 6.85/7.04  thf('23', plain,
% 6.85/7.04      (![X19 : $i, X20 : $i]:
% 6.85/7.04         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 6.85/7.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.85/7.04  thf('24', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.04         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 6.85/7.04           = (X0))),
% 6.85/7.04      inference('sup-', [status(thm)], ['22', '23'])).
% 6.85/7.04  thf(t17_xboole_1, axiom,
% 6.85/7.04    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 6.85/7.04  thf('25', plain,
% 6.85/7.04      (![X21 : $i, X22 : $i]: (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ X21)),
% 6.85/7.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.85/7.04  thf(t28_xboole_1, axiom,
% 6.85/7.04    (![A:$i,B:$i]:
% 6.85/7.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.85/7.04  thf('26', plain,
% 6.85/7.04      (![X29 : $i, X30 : $i]:
% 6.85/7.04         (((k3_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_tarski @ X29 @ X30))),
% 6.85/7.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.85/7.04  thf('27', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i]:
% 6.85/7.04         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 6.85/7.04           = (k3_xboole_0 @ X0 @ X1))),
% 6.85/7.04      inference('sup-', [status(thm)], ['25', '26'])).
% 6.85/7.04  thf(t29_xboole_1, axiom,
% 6.85/7.04    (![A:$i,B:$i,C:$i]:
% 6.85/7.04     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 6.85/7.04  thf('28', plain,
% 6.85/7.04      (![X31 : $i, X32 : $i, X33 : $i]:
% 6.85/7.04         (r1_tarski @ (k3_xboole_0 @ X31 @ X32) @ (k2_xboole_0 @ X31 @ X33))),
% 6.85/7.04      inference('cnf', [status(esa)], [t29_xboole_1])).
% 6.85/7.04  thf('29', plain,
% 6.85/7.04      (![X29 : $i, X30 : $i]:
% 6.85/7.04         (((k3_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_tarski @ X29 @ X30))),
% 6.85/7.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.85/7.04  thf('30', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.04         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 6.85/7.04           = (k3_xboole_0 @ X1 @ X2))),
% 6.85/7.04      inference('sup-', [status(thm)], ['28', '29'])).
% 6.85/7.04  thf('31', plain,
% 6.85/7.04      (![X12 : $i, X14 : $i, X15 : $i]:
% 6.85/7.04         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 6.85/7.04          | ~ (r1_xboole_0 @ X12 @ X15))),
% 6.85/7.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 6.85/7.04  thf('32', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.85/7.04         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X0))
% 6.85/7.04          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X2)))),
% 6.85/7.04      inference('sup-', [status(thm)], ['30', '31'])).
% 6.85/7.04  thf('33', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.85/7.04         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 6.85/7.04             (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 6.85/7.04          | ~ (r2_hidden @ X3 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 6.85/7.04      inference('sup-', [status(thm)], ['27', '32'])).
% 6.85/7.04  thf('34', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i]:
% 6.85/7.04         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 6.85/7.04           = (k3_xboole_0 @ X0 @ X1))),
% 6.85/7.04      inference('sup-', [status(thm)], ['25', '26'])).
% 6.85/7.04  thf('35', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.85/7.04         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 6.85/7.04             (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 6.85/7.04          | ~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.85/7.04      inference('demod', [status(thm)], ['33', '34'])).
% 6.85/7.04  thf('36', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.85/7.04         (~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 6.85/7.04          | ~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 6.85/7.04      inference('sup-', [status(thm)], ['24', '35'])).
% 6.85/7.04  thf('37', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i]:
% 6.85/7.04         ~ (r2_hidden @ X1 @ 
% 6.85/7.04            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_2) @ 
% 6.85/7.04             (k3_xboole_0 @ X0 @ sk_A)))),
% 6.85/7.04      inference('sup-', [status(thm)], ['6', '36'])).
% 6.85/7.04  thf('38', plain,
% 6.85/7.04      (![X0 : $i]:
% 6.85/7.04         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_2) @ 
% 6.85/7.04          (k3_xboole_0 @ X0 @ sk_A))),
% 6.85/7.04      inference('sup-', [status(thm)], ['1', '37'])).
% 6.85/7.04  thf('39', plain,
% 6.85/7.04      (![X6 : $i, X7 : $i]:
% 6.85/7.04         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 6.85/7.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 6.85/7.04  thf('40', plain,
% 6.85/7.04      (![X0 : $i]:
% 6.85/7.04         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ 
% 6.85/7.04          (k3_xboole_0 @ sk_B @ sk_C_2))),
% 6.85/7.04      inference('sup-', [status(thm)], ['38', '39'])).
% 6.85/7.04  thf('41', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i]:
% 6.85/7.04         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 6.85/7.04      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.85/7.04  thf('42', plain,
% 6.85/7.04      (![X0 : $i]:
% 6.85/7.04         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ 
% 6.85/7.04           (k3_xboole_0 @ sk_B @ sk_C_2)) = (k1_xboole_0))),
% 6.85/7.04      inference('sup-', [status(thm)], ['40', '41'])).
% 6.85/7.04  thf('43', plain,
% 6.85/7.04      (![X21 : $i, X22 : $i]: (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ X21)),
% 6.85/7.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.85/7.04  thf(t26_xboole_1, axiom,
% 6.85/7.04    (![A:$i,B:$i,C:$i]:
% 6.85/7.04     ( ( r1_tarski @ A @ B ) =>
% 6.85/7.04       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ))).
% 6.85/7.04  thf('44', plain,
% 6.85/7.04      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.85/7.04         (~ (r1_tarski @ X26 @ X27)
% 6.85/7.04          | (r1_tarski @ (k3_xboole_0 @ X26 @ X28) @ (k3_xboole_0 @ X27 @ X28)))),
% 6.85/7.04      inference('cnf', [status(esa)], [t26_xboole_1])).
% 6.85/7.04  thf('45', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.04         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 6.85/7.04          (k3_xboole_0 @ X0 @ X2))),
% 6.85/7.04      inference('sup-', [status(thm)], ['43', '44'])).
% 6.85/7.04  thf('46', plain,
% 6.85/7.04      (![X21 : $i, X22 : $i]: (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ X21)),
% 6.85/7.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.85/7.04  thf(t19_xboole_1, axiom,
% 6.85/7.04    (![A:$i,B:$i,C:$i]:
% 6.85/7.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 6.85/7.04       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 6.85/7.04  thf('47', plain,
% 6.85/7.04      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.85/7.04         (~ (r1_tarski @ X23 @ X24)
% 6.85/7.04          | ~ (r1_tarski @ X23 @ X25)
% 6.85/7.04          | (r1_tarski @ X23 @ (k3_xboole_0 @ X24 @ X25)))),
% 6.85/7.04      inference('cnf', [status(esa)], [t19_xboole_1])).
% 6.85/7.04  thf('48', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.04         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 6.85/7.04          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 6.85/7.04      inference('sup-', [status(thm)], ['46', '47'])).
% 6.85/7.04  thf('49', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.04         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ 
% 6.85/7.04          (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 6.85/7.04      inference('sup-', [status(thm)], ['45', '48'])).
% 6.85/7.04  thf('50', plain,
% 6.85/7.04      ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C_2) @ 
% 6.85/7.04        k1_xboole_0)),
% 6.85/7.04      inference('sup+', [status(thm)], ['42', '49'])).
% 6.85/7.04  thf('51', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 6.85/7.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.04  thf('52', plain,
% 6.85/7.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.04         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 6.85/7.04      inference('sup-', [status(thm)], ['19', '20'])).
% 6.85/7.04  thf('53', plain,
% 6.85/7.04      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C_2)),
% 6.85/7.04      inference('sup-', [status(thm)], ['51', '52'])).
% 6.85/7.04  thf('54', plain,
% 6.85/7.04      (![X29 : $i, X30 : $i]:
% 6.85/7.04         (((k3_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_tarski @ X29 @ X30))),
% 6.85/7.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.85/7.04  thf('55', plain,
% 6.85/7.04      (![X0 : $i]:
% 6.85/7.04         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C_2)
% 6.85/7.04           = (k3_xboole_0 @ X0 @ sk_A))),
% 6.85/7.04      inference('sup-', [status(thm)], ['53', '54'])).
% 6.85/7.04  thf('56', plain, ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)),
% 6.85/7.04      inference('demod', [status(thm)], ['50', '55'])).
% 6.85/7.04  thf('57', plain,
% 6.85/7.04      (![X29 : $i, X30 : $i]:
% 6.85/7.04         (((k3_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_tarski @ X29 @ X30))),
% 6.85/7.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.85/7.04  thf('58', plain,
% 6.85/7.04      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ k1_xboole_0)
% 6.85/7.04         = (k3_xboole_0 @ sk_B @ sk_A))),
% 6.85/7.04      inference('sup-', [status(thm)], ['56', '57'])).
% 6.85/7.04  thf('59', plain,
% 6.85/7.04      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.85/7.04      inference('sup-', [status(thm)], ['7', '8'])).
% 6.85/7.04  thf('60', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 6.85/7.04      inference('demod', [status(thm)], ['58', '59'])).
% 6.85/7.04  thf('61', plain,
% 6.85/7.04      (![X0 : $i, X2 : $i]:
% 6.85/7.04         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 6.85/7.04      inference('cnf', [status(esa)], [d7_xboole_0])).
% 6.85/7.04  thf('62', plain,
% 6.85/7.04      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 6.85/7.04      inference('sup-', [status(thm)], ['60', '61'])).
% 6.85/7.04  thf('63', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 6.85/7.04      inference('simplify', [status(thm)], ['62'])).
% 6.85/7.04  thf('64', plain,
% 6.85/7.04      (![X6 : $i, X7 : $i]:
% 6.85/7.04         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 6.85/7.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 6.85/7.04  thf('65', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 6.85/7.04      inference('sup-', [status(thm)], ['63', '64'])).
% 6.85/7.04  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 6.85/7.04  
% 6.85/7.04  % SZS output end Refutation
% 6.85/7.04  
% 6.85/7.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
