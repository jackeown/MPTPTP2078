%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TDinjHgYcz

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:25 EST 2020

% Result     : Theorem 12.40s
% Output     : Refutation 12.40s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 147 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  630 (1186 expanded)
%              Number of equality atoms :   44 (  69 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k3_xboole_0 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k3_xboole_0 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','15','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k3_xboole_0 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('19',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
      | ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ( r1_xboole_0 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','33','34','37','48'])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('52',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['59'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','62'])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('65',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TDinjHgYcz
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 12.40/12.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.40/12.59  % Solved by: fo/fo7.sh
% 12.40/12.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.40/12.59  % done 9282 iterations in 12.130s
% 12.40/12.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.40/12.59  % SZS output start Refutation
% 12.40/12.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 12.40/12.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 12.40/12.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.40/12.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.40/12.59  thf(sk_A_type, type, sk_A: $i).
% 12.40/12.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.40/12.59  thf(sk_B_type, type, sk_B: $i).
% 12.40/12.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.40/12.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 12.40/12.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 12.40/12.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.40/12.59  thf(t149_zfmisc_1, conjecture,
% 12.40/12.59    (![A:$i,B:$i,C:$i,D:$i]:
% 12.40/12.59     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 12.40/12.59         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 12.40/12.59       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 12.40/12.59  thf(zf_stmt_0, negated_conjecture,
% 12.40/12.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 12.40/12.59        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 12.40/12.59            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 12.40/12.59          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 12.40/12.59    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 12.40/12.59  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 12.40/12.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.40/12.59  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 12.40/12.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.40/12.59  thf(symmetry_r1_xboole_0, axiom,
% 12.40/12.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 12.40/12.59  thf('2', plain,
% 12.40/12.59      (![X11 : $i, X12 : $i]:
% 12.40/12.59         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 12.40/12.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 12.40/12.59  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 12.40/12.59      inference('sup-', [status(thm)], ['1', '2'])).
% 12.40/12.59  thf('4', plain,
% 12.40/12.59      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 12.40/12.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.40/12.59  thf(commutativity_k3_xboole_0, axiom,
% 12.40/12.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 12.40/12.59  thf('5', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.40/12.59  thf('6', plain,
% 12.40/12.59      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 12.40/12.59      inference('demod', [status(thm)], ['4', '5'])).
% 12.40/12.59  thf(t28_xboole_1, axiom,
% 12.40/12.59    (![A:$i,B:$i]:
% 12.40/12.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 12.40/12.59  thf('7', plain,
% 12.40/12.59      (![X20 : $i, X21 : $i]:
% 12.40/12.59         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 12.40/12.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 12.40/12.59  thf('8', plain,
% 12.40/12.59      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 12.40/12.59         = (k3_xboole_0 @ sk_B @ sk_A))),
% 12.40/12.59      inference('sup-', [status(thm)], ['6', '7'])).
% 12.40/12.59  thf('9', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.40/12.59  thf(t16_xboole_1, axiom,
% 12.40/12.59    (![A:$i,B:$i,C:$i]:
% 12.40/12.59     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 12.40/12.59       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 12.40/12.59  thf('10', plain,
% 12.40/12.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.40/12.59         ((k3_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19)
% 12.40/12.59           = (k3_xboole_0 @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 12.40/12.59      inference('cnf', [status(esa)], [t16_xboole_1])).
% 12.40/12.59  thf('11', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.40/12.59         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 12.40/12.59           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 12.40/12.59      inference('sup+', [status(thm)], ['9', '10'])).
% 12.40/12.59  thf('12', plain,
% 12.40/12.59      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)))
% 12.40/12.59         = (k3_xboole_0 @ sk_B @ sk_A))),
% 12.40/12.59      inference('demod', [status(thm)], ['8', '11'])).
% 12.40/12.59  thf('13', plain,
% 12.40/12.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.40/12.59         ((k3_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19)
% 12.40/12.59           = (k3_xboole_0 @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 12.40/12.59      inference('cnf', [status(esa)], [t16_xboole_1])).
% 12.40/12.59  thf('14', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.40/12.59  thf('15', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.40/12.59         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 12.40/12.59           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 12.40/12.59      inference('sup+', [status(thm)], ['13', '14'])).
% 12.40/12.59  thf('16', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.40/12.59  thf('17', plain,
% 12.40/12.59      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))
% 12.40/12.59         = (k3_xboole_0 @ sk_B @ sk_A))),
% 12.40/12.59      inference('demod', [status(thm)], ['12', '15', '16'])).
% 12.40/12.59  thf('18', plain,
% 12.40/12.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 12.40/12.59         ((k3_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19)
% 12.40/12.59           = (k3_xboole_0 @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 12.40/12.59      inference('cnf', [status(esa)], [t16_xboole_1])).
% 12.40/12.59  thf(l27_zfmisc_1, axiom,
% 12.40/12.59    (![A:$i,B:$i]:
% 12.40/12.59     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 12.40/12.59  thf('19', plain,
% 12.40/12.59      (![X35 : $i, X36 : $i]:
% 12.40/12.59         ((r1_xboole_0 @ (k1_tarski @ X35) @ X36) | (r2_hidden @ X35 @ X36))),
% 12.40/12.59      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 12.40/12.59  thf(d7_xboole_0, axiom,
% 12.40/12.59    (![A:$i,B:$i]:
% 12.40/12.59     ( ( r1_xboole_0 @ A @ B ) <=>
% 12.40/12.59       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 12.40/12.59  thf('20', plain,
% 12.40/12.59      (![X8 : $i, X9 : $i]:
% 12.40/12.59         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 12.40/12.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 12.40/12.59  thf('21', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]:
% 12.40/12.59         ((r2_hidden @ X1 @ X0)
% 12.40/12.59          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 12.40/12.59      inference('sup-', [status(thm)], ['19', '20'])).
% 12.40/12.59  thf('22', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.40/12.59  thf('23', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]:
% 12.40/12.59         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 12.40/12.59          | (r2_hidden @ X0 @ X1))),
% 12.40/12.59      inference('sup+', [status(thm)], ['21', '22'])).
% 12.40/12.59  thf('24', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.40/12.59         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 12.40/12.59            = (k1_xboole_0))
% 12.40/12.59          | (r2_hidden @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 12.40/12.59      inference('sup+', [status(thm)], ['18', '23'])).
% 12.40/12.59  thf('25', plain,
% 12.40/12.59      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 12.40/12.59        | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 12.40/12.59      inference('sup+', [status(thm)], ['17', '24'])).
% 12.40/12.59  thf('26', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 12.40/12.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.40/12.59  thf(d4_xboole_0, axiom,
% 12.40/12.59    (![A:$i,B:$i,C:$i]:
% 12.40/12.59     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 12.40/12.59       ( ![D:$i]:
% 12.40/12.59         ( ( r2_hidden @ D @ C ) <=>
% 12.40/12.59           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 12.40/12.59  thf('27', plain,
% 12.40/12.59      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 12.40/12.59         (~ (r2_hidden @ X2 @ X3)
% 12.40/12.59          | ~ (r2_hidden @ X2 @ X4)
% 12.40/12.59          | (r2_hidden @ X2 @ X5)
% 12.40/12.59          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 12.40/12.59      inference('cnf', [status(esa)], [d4_xboole_0])).
% 12.40/12.59  thf('28', plain,
% 12.40/12.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 12.40/12.59         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 12.40/12.59          | ~ (r2_hidden @ X2 @ X4)
% 12.40/12.59          | ~ (r2_hidden @ X2 @ X3))),
% 12.40/12.59      inference('simplify', [status(thm)], ['27'])).
% 12.40/12.59  thf('29', plain,
% 12.40/12.59      (![X0 : $i]:
% 12.40/12.59         (~ (r2_hidden @ sk_D_1 @ X0)
% 12.40/12.59          | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ X0 @ sk_C_1)))),
% 12.40/12.59      inference('sup-', [status(thm)], ['26', '28'])).
% 12.40/12.59  thf('30', plain,
% 12.40/12.59      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 12.40/12.59        | (r2_hidden @ sk_D_1 @ 
% 12.40/12.59           (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C_1)))),
% 12.40/12.59      inference('sup-', [status(thm)], ['25', '29'])).
% 12.40/12.59  thf('31', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.40/12.59         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 12.40/12.59           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 12.40/12.59      inference('sup+', [status(thm)], ['13', '14'])).
% 12.40/12.59  thf('32', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.40/12.59  thf('33', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.40/12.59         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1)
% 12.40/12.59           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 12.40/12.59      inference('sup+', [status(thm)], ['31', '32'])).
% 12.40/12.59  thf('34', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.40/12.59  thf('35', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 12.40/12.59      inference('sup-', [status(thm)], ['1', '2'])).
% 12.40/12.59  thf('36', plain,
% 12.40/12.59      (![X8 : $i, X9 : $i]:
% 12.40/12.59         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 12.40/12.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 12.40/12.59  thf('37', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 12.40/12.59      inference('sup-', [status(thm)], ['35', '36'])).
% 12.40/12.59  thf('38', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 12.40/12.59      inference('sup-', [status(thm)], ['1', '2'])).
% 12.40/12.59  thf(t74_xboole_1, axiom,
% 12.40/12.59    (![A:$i,B:$i,C:$i]:
% 12.40/12.59     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 12.40/12.59          ( r1_xboole_0 @ A @ B ) ) ))).
% 12.40/12.59  thf('39', plain,
% 12.40/12.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 12.40/12.59         (~ (r1_xboole_0 @ X26 @ X27)
% 12.40/12.59          | (r1_xboole_0 @ X26 @ (k3_xboole_0 @ X27 @ X28)))),
% 12.40/12.59      inference('cnf', [status(esa)], [t74_xboole_1])).
% 12.40/12.59  thf('40', plain,
% 12.40/12.59      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0))),
% 12.40/12.59      inference('sup-', [status(thm)], ['38', '39'])).
% 12.40/12.59  thf('41', plain,
% 12.40/12.59      (![X11 : $i, X12 : $i]:
% 12.40/12.59         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 12.40/12.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 12.40/12.59  thf('42', plain,
% 12.40/12.59      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 12.40/12.59      inference('sup-', [status(thm)], ['40', '41'])).
% 12.40/12.59  thf('43', plain,
% 12.40/12.59      (![X8 : $i, X9 : $i]:
% 12.40/12.59         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 12.40/12.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 12.40/12.59  thf('44', plain,
% 12.40/12.59      (![X0 : $i]:
% 12.40/12.59         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B) = (k1_xboole_0))),
% 12.40/12.59      inference('sup-', [status(thm)], ['42', '43'])).
% 12.40/12.59  thf('45', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.40/12.59         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 12.40/12.59           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 12.40/12.59      inference('sup+', [status(thm)], ['9', '10'])).
% 12.40/12.59  thf('46', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.40/12.59  thf('47', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 12.40/12.59      inference('sup-', [status(thm)], ['35', '36'])).
% 12.40/12.59  thf('48', plain,
% 12.40/12.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 12.40/12.59      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 12.40/12.59  thf('49', plain,
% 12.40/12.59      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 12.40/12.59        | (r2_hidden @ sk_D_1 @ k1_xboole_0))),
% 12.40/12.59      inference('demod', [status(thm)], ['30', '33', '34', '37', '48'])).
% 12.40/12.59  thf('50', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 12.40/12.59      inference('sup-', [status(thm)], ['35', '36'])).
% 12.40/12.59  thf('51', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.40/12.59  thf(t4_xboole_0, axiom,
% 12.40/12.59    (![A:$i,B:$i]:
% 12.40/12.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 12.40/12.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 12.40/12.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 12.40/12.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 12.40/12.59  thf('52', plain,
% 12.40/12.59      (![X13 : $i, X15 : $i, X16 : $i]:
% 12.40/12.59         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 12.40/12.59          | ~ (r1_xboole_0 @ X13 @ X16))),
% 12.40/12.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 12.40/12.59  thf('53', plain,
% 12.40/12.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.40/12.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 12.40/12.59          | ~ (r1_xboole_0 @ X0 @ X1))),
% 12.40/12.59      inference('sup-', [status(thm)], ['51', '52'])).
% 12.40/12.59  thf('54', plain,
% 12.40/12.59      (![X0 : $i]:
% 12.40/12.59         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_C_1 @ sk_B))),
% 12.40/12.59      inference('sup-', [status(thm)], ['50', '53'])).
% 12.40/12.59  thf('55', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 12.40/12.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.40/12.59  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 12.40/12.59      inference('demod', [status(thm)], ['54', '55'])).
% 12.40/12.59  thf('57', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 12.40/12.59      inference('clc', [status(thm)], ['49', '56'])).
% 12.40/12.59  thf('58', plain,
% 12.40/12.59      (![X8 : $i, X10 : $i]:
% 12.40/12.59         ((r1_xboole_0 @ X8 @ X10)
% 12.40/12.59          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 12.40/12.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 12.40/12.59  thf('59', plain,
% 12.40/12.59      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 12.40/12.59      inference('sup-', [status(thm)], ['57', '58'])).
% 12.40/12.59  thf('60', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 12.40/12.59      inference('simplify', [status(thm)], ['59'])).
% 12.40/12.59  thf(t70_xboole_1, axiom,
% 12.40/12.59    (![A:$i,B:$i,C:$i]:
% 12.40/12.59     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 12.40/12.59            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 12.40/12.59       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 12.40/12.59            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 12.40/12.59  thf('61', plain,
% 12.40/12.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 12.40/12.59         ((r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 12.40/12.59          | ~ (r1_xboole_0 @ X22 @ X23)
% 12.40/12.59          | ~ (r1_xboole_0 @ X22 @ X24))),
% 12.40/12.59      inference('cnf', [status(esa)], [t70_xboole_1])).
% 12.40/12.59  thf('62', plain,
% 12.40/12.59      (![X0 : $i]:
% 12.40/12.59         (~ (r1_xboole_0 @ sk_B @ X0)
% 12.40/12.59          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 12.40/12.59      inference('sup-', [status(thm)], ['60', '61'])).
% 12.40/12.59  thf('63', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 12.40/12.59      inference('sup-', [status(thm)], ['3', '62'])).
% 12.40/12.59  thf('64', plain,
% 12.40/12.59      (![X11 : $i, X12 : $i]:
% 12.40/12.59         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 12.40/12.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 12.40/12.59  thf('65', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 12.40/12.59      inference('sup-', [status(thm)], ['63', '64'])).
% 12.40/12.59  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 12.40/12.59  
% 12.40/12.59  % SZS output end Refutation
% 12.40/12.59  
% 12.40/12.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
