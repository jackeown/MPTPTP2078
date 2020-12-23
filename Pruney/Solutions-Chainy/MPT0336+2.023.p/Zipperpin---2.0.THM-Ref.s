%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J64jxxVvpo

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:23 EST 2020

% Result     : Theorem 49.57s
% Output     : Refutation 49.57s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 117 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   19
%              Number of atoms          :  637 ( 991 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X17 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X17 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X17 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ X38 @ ( k1_tarski @ X39 ) )
        = X38 )
      | ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_xboole_0 @ X28 @ X30 )
      | ( ( k4_xboole_0 @ X28 @ X30 )
       != X28 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ( r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    r2_hidden @ sk_D_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ( r1_xboole_0 @ X31 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','52'])).

thf('54',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','53'])).

thf('55',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('57',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('60',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('65',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['2','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J64jxxVvpo
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 49.57/49.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 49.57/49.81  % Solved by: fo/fo7.sh
% 49.57/49.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 49.57/49.81  % done 38290 iterations in 49.375s
% 49.57/49.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 49.57/49.81  % SZS output start Refutation
% 49.57/49.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 49.57/49.81  thf(sk_A_type, type, sk_A: $i).
% 49.57/49.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 49.57/49.81  thf(sk_B_type, type, sk_B: $i).
% 49.57/49.81  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 49.57/49.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 49.57/49.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 49.57/49.81  thf(sk_C_2_type, type, sk_C_2: $i).
% 49.57/49.81  thf(sk_D_1_type, type, sk_D_1: $i).
% 49.57/49.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 49.57/49.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 49.57/49.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 49.57/49.81  thf(t149_zfmisc_1, conjecture,
% 49.57/49.81    (![A:$i,B:$i,C:$i,D:$i]:
% 49.57/49.81     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 49.57/49.81         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 49.57/49.81       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 49.57/49.81  thf(zf_stmt_0, negated_conjecture,
% 49.57/49.81    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 49.57/49.81        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 49.57/49.81            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 49.57/49.81          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 49.57/49.81    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 49.57/49.81  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 49.57/49.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.57/49.81  thf(commutativity_k2_xboole_0, axiom,
% 49.57/49.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 49.57/49.81  thf('1', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.57/49.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.57/49.81  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 49.57/49.81      inference('demod', [status(thm)], ['0', '1'])).
% 49.57/49.81  thf(t4_xboole_0, axiom,
% 49.57/49.81    (![A:$i,B:$i]:
% 49.57/49.81     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 49.57/49.81            ( r1_xboole_0 @ A @ B ) ) ) & 
% 49.57/49.81       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 49.57/49.81            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 49.57/49.81  thf('3', plain,
% 49.57/49.81      (![X17 : $i, X18 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X17 @ X18)
% 49.57/49.81          | (r2_hidden @ (sk_C_1 @ X18 @ X17) @ (k3_xboole_0 @ X17 @ X18)))),
% 49.57/49.81      inference('cnf', [status(esa)], [t4_xboole_0])).
% 49.57/49.81  thf(t48_xboole_1, axiom,
% 49.57/49.81    (![A:$i,B:$i]:
% 49.57/49.81     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 49.57/49.81  thf('4', plain,
% 49.57/49.81      (![X22 : $i, X23 : $i]:
% 49.57/49.81         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 49.57/49.81           = (k3_xboole_0 @ X22 @ X23))),
% 49.57/49.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 49.57/49.81  thf(d5_xboole_0, axiom,
% 49.57/49.81    (![A:$i,B:$i,C:$i]:
% 49.57/49.81     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 49.57/49.81       ( ![D:$i]:
% 49.57/49.81         ( ( r2_hidden @ D @ C ) <=>
% 49.57/49.81           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 49.57/49.81  thf('5', plain,
% 49.57/49.81      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 49.57/49.81         (~ (r2_hidden @ X6 @ X5)
% 49.57/49.81          | (r2_hidden @ X6 @ X3)
% 49.57/49.81          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 49.57/49.81      inference('cnf', [status(esa)], [d5_xboole_0])).
% 49.57/49.81  thf('6', plain,
% 49.57/49.81      (![X3 : $i, X4 : $i, X6 : $i]:
% 49.57/49.81         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 49.57/49.81      inference('simplify', [status(thm)], ['5'])).
% 49.57/49.81  thf('7', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.57/49.81         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 49.57/49.81      inference('sup-', [status(thm)], ['4', '6'])).
% 49.57/49.81  thf('8', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1))),
% 49.57/49.81      inference('sup-', [status(thm)], ['3', '7'])).
% 49.57/49.81  thf('9', plain,
% 49.57/49.81      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 49.57/49.81         (~ (r2_hidden @ X2 @ X3)
% 49.57/49.81          | (r2_hidden @ X2 @ X4)
% 49.57/49.81          | (r2_hidden @ X2 @ X5)
% 49.57/49.81          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 49.57/49.81      inference('cnf', [status(esa)], [d5_xboole_0])).
% 49.57/49.81  thf('10', plain,
% 49.57/49.81      (![X2 : $i, X3 : $i, X4 : $i]:
% 49.57/49.81         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 49.57/49.81          | (r2_hidden @ X2 @ X4)
% 49.57/49.81          | ~ (r2_hidden @ X2 @ X3))),
% 49.57/49.81      inference('simplify', [status(thm)], ['9'])).
% 49.57/49.81  thf('11', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X0 @ X1)
% 49.57/49.81          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2)
% 49.57/49.81          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 49.57/49.81      inference('sup-', [status(thm)], ['8', '10'])).
% 49.57/49.81  thf('12', plain,
% 49.57/49.81      (![X17 : $i, X18 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X17 @ X18)
% 49.57/49.81          | (r2_hidden @ (sk_C_1 @ X18 @ X17) @ (k3_xboole_0 @ X17 @ X18)))),
% 49.57/49.81      inference('cnf', [status(esa)], [t4_xboole_0])).
% 49.57/49.81  thf('13', plain,
% 49.57/49.81      (![X22 : $i, X23 : $i]:
% 49.57/49.81         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 49.57/49.81           = (k3_xboole_0 @ X22 @ X23))),
% 49.57/49.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 49.57/49.81  thf('14', plain,
% 49.57/49.81      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 49.57/49.81         (~ (r2_hidden @ X6 @ X5)
% 49.57/49.81          | ~ (r2_hidden @ X6 @ X4)
% 49.57/49.81          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 49.57/49.81      inference('cnf', [status(esa)], [d5_xboole_0])).
% 49.57/49.81  thf('15', plain,
% 49.57/49.81      (![X3 : $i, X4 : $i, X6 : $i]:
% 49.57/49.81         (~ (r2_hidden @ X6 @ X4)
% 49.57/49.81          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 49.57/49.81      inference('simplify', [status(thm)], ['14'])).
% 49.57/49.81  thf('16', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.57/49.81         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 49.57/49.81          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 49.57/49.81      inference('sup-', [status(thm)], ['13', '15'])).
% 49.57/49.81  thf('17', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X1 @ X0)
% 49.57/49.81          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 49.57/49.81      inference('sup-', [status(thm)], ['12', '16'])).
% 49.57/49.81  thf('18', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i]:
% 49.57/49.81         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0)
% 49.57/49.81          | (r1_xboole_0 @ X1 @ X0)
% 49.57/49.81          | (r1_xboole_0 @ X1 @ X0))),
% 49.57/49.81      inference('sup-', [status(thm)], ['11', '17'])).
% 49.57/49.81  thf('19', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0))),
% 49.57/49.81      inference('simplify', [status(thm)], ['18'])).
% 49.57/49.81  thf('20', plain,
% 49.57/49.81      (![X17 : $i, X18 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X17 @ X18)
% 49.57/49.81          | (r2_hidden @ (sk_C_1 @ X18 @ X17) @ (k3_xboole_0 @ X17 @ X18)))),
% 49.57/49.81      inference('cnf', [status(esa)], [t4_xboole_0])).
% 49.57/49.81  thf(t65_zfmisc_1, axiom,
% 49.57/49.81    (![A:$i,B:$i]:
% 49.57/49.81     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 49.57/49.81       ( ~( r2_hidden @ B @ A ) ) ))).
% 49.57/49.81  thf('21', plain,
% 49.57/49.81      (![X38 : $i, X39 : $i]:
% 49.57/49.81         (((k4_xboole_0 @ X38 @ (k1_tarski @ X39)) = (X38))
% 49.57/49.81          | (r2_hidden @ X39 @ X38))),
% 49.57/49.81      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 49.57/49.81  thf(t83_xboole_1, axiom,
% 49.57/49.81    (![A:$i,B:$i]:
% 49.57/49.81     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 49.57/49.81  thf('22', plain,
% 49.57/49.81      (![X28 : $i, X30 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X28 @ X30) | ((k4_xboole_0 @ X28 @ X30) != (X28)))),
% 49.57/49.81      inference('cnf', [status(esa)], [t83_xboole_1])).
% 49.57/49.81  thf('23', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i]:
% 49.57/49.81         (((X0) != (X0))
% 49.57/49.81          | (r2_hidden @ X1 @ X0)
% 49.57/49.81          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 49.57/49.81      inference('sup-', [status(thm)], ['21', '22'])).
% 49.57/49.81  thf('24', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 49.57/49.81      inference('simplify', [status(thm)], ['23'])).
% 49.57/49.81  thf(symmetry_r1_xboole_0, axiom,
% 49.57/49.81    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 49.57/49.81  thf('25', plain,
% 49.57/49.81      (![X11 : $i, X12 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 49.57/49.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 49.57/49.81  thf('26', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i]:
% 49.57/49.81         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 49.57/49.81      inference('sup-', [status(thm)], ['24', '25'])).
% 49.57/49.81  thf(t70_xboole_1, axiom,
% 49.57/49.81    (![A:$i,B:$i,C:$i]:
% 49.57/49.81     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 49.57/49.81            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 49.57/49.81       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 49.57/49.81            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 49.57/49.81  thf('27', plain,
% 49.57/49.81      (![X24 : $i, X25 : $i, X27 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X24 @ X25)
% 49.57/49.81          | ~ (r1_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X27)))),
% 49.57/49.81      inference('cnf', [status(esa)], [t70_xboole_1])).
% 49.57/49.81  thf('28', plain,
% 49.57/49.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.57/49.81         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 49.57/49.81          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 49.57/49.81      inference('sup-', [status(thm)], ['26', '27'])).
% 49.57/49.81  thf('29', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 49.57/49.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.57/49.81  thf('30', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 49.57/49.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.57/49.81  thf('31', plain,
% 49.57/49.81      (![X24 : $i, X25 : $i, X26 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 49.57/49.81          | ~ (r1_xboole_0 @ X24 @ X25)
% 49.57/49.81          | ~ (r1_xboole_0 @ X24 @ X26))),
% 49.57/49.81      inference('cnf', [status(esa)], [t70_xboole_1])).
% 49.57/49.81  thf('32', plain,
% 49.57/49.81      (![X0 : $i]:
% 49.57/49.81         (~ (r1_xboole_0 @ sk_C_2 @ X0)
% 49.57/49.81          | (r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ X0)))),
% 49.57/49.81      inference('sup-', [status(thm)], ['30', '31'])).
% 49.57/49.81  thf('33', plain, ((r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 49.57/49.81      inference('sup-', [status(thm)], ['29', '32'])).
% 49.57/49.81  thf('34', plain, ((r2_hidden @ sk_D_1 @ sk_C_2)),
% 49.57/49.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.57/49.81  thf(t3_xboole_0, axiom,
% 49.57/49.81    (![A:$i,B:$i]:
% 49.57/49.81     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 49.57/49.81            ( r1_xboole_0 @ A @ B ) ) ) & 
% 49.57/49.81       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 49.57/49.81            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 49.57/49.81  thf('35', plain,
% 49.57/49.81      (![X13 : $i, X15 : $i, X16 : $i]:
% 49.57/49.81         (~ (r2_hidden @ X15 @ X13)
% 49.57/49.81          | ~ (r2_hidden @ X15 @ X16)
% 49.57/49.81          | ~ (r1_xboole_0 @ X13 @ X16))),
% 49.57/49.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 49.57/49.81  thf('36', plain,
% 49.57/49.81      (![X0 : $i]:
% 49.57/49.81         (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 49.57/49.81      inference('sup-', [status(thm)], ['34', '35'])).
% 49.57/49.81  thf('37', plain, (~ (r2_hidden @ sk_D_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 49.57/49.81      inference('sup-', [status(thm)], ['33', '36'])).
% 49.57/49.81  thf('38', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_B)),
% 49.57/49.81      inference('sup-', [status(thm)], ['28', '37'])).
% 49.57/49.81  thf('39', plain,
% 49.57/49.81      (![X11 : $i, X12 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 49.57/49.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 49.57/49.81  thf('40', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1))),
% 49.57/49.81      inference('sup-', [status(thm)], ['38', '39'])).
% 49.57/49.81  thf('41', plain,
% 49.57/49.81      (![X28 : $i, X29 : $i]:
% 49.57/49.81         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 49.57/49.81      inference('cnf', [status(esa)], [t83_xboole_1])).
% 49.57/49.81  thf('42', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)) = (sk_B))),
% 49.57/49.81      inference('sup-', [status(thm)], ['40', '41'])).
% 49.57/49.81  thf('43', plain,
% 49.57/49.81      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 49.57/49.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.57/49.81  thf(t85_xboole_1, axiom,
% 49.57/49.81    (![A:$i,B:$i,C:$i]:
% 49.57/49.81     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 49.57/49.81  thf('44', plain,
% 49.57/49.81      (![X31 : $i, X32 : $i, X33 : $i]:
% 49.57/49.81         (~ (r1_tarski @ X31 @ X32)
% 49.57/49.81          | (r1_xboole_0 @ X31 @ (k4_xboole_0 @ X33 @ X32)))),
% 49.57/49.81      inference('cnf', [status(esa)], [t85_xboole_1])).
% 49.57/49.81  thf('45', plain,
% 49.57/49.81      (![X0 : $i]:
% 49.57/49.81         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 49.57/49.81          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))),
% 49.57/49.81      inference('sup-', [status(thm)], ['43', '44'])).
% 49.57/49.81  thf('46', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 49.57/49.81      inference('sup+', [status(thm)], ['42', '45'])).
% 49.57/49.81  thf('47', plain,
% 49.57/49.81      (![X11 : $i, X12 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 49.57/49.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 49.57/49.81  thf('48', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))),
% 49.57/49.81      inference('sup-', [status(thm)], ['46', '47'])).
% 49.57/49.81  thf('49', plain,
% 49.57/49.81      (![X28 : $i, X29 : $i]:
% 49.57/49.81         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 49.57/49.81      inference('cnf', [status(esa)], [t83_xboole_1])).
% 49.57/49.81  thf('50', plain,
% 49.57/49.81      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 49.57/49.81      inference('sup-', [status(thm)], ['48', '49'])).
% 49.57/49.81  thf('51', plain,
% 49.57/49.81      (![X3 : $i, X4 : $i, X6 : $i]:
% 49.57/49.81         (~ (r2_hidden @ X6 @ X4)
% 49.57/49.81          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 49.57/49.81      inference('simplify', [status(thm)], ['14'])).
% 49.57/49.81  thf('52', plain,
% 49.57/49.81      (![X0 : $i]:
% 49.57/49.81         (~ (r2_hidden @ X0 @ sk_B)
% 49.57/49.81          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 49.57/49.81      inference('sup-', [status(thm)], ['50', '51'])).
% 49.57/49.81  thf('53', plain,
% 49.57/49.81      (((r1_xboole_0 @ sk_A @ sk_B)
% 49.57/49.81        | ~ (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ sk_B))),
% 49.57/49.81      inference('sup-', [status(thm)], ['20', '52'])).
% 49.57/49.81  thf('54', plain,
% 49.57/49.81      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_A @ sk_B))),
% 49.57/49.81      inference('sup-', [status(thm)], ['19', '53'])).
% 49.57/49.81  thf('55', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 49.57/49.81      inference('simplify', [status(thm)], ['54'])).
% 49.57/49.81  thf('56', plain,
% 49.57/49.81      (![X11 : $i, X12 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 49.57/49.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 49.57/49.81  thf('57', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 49.57/49.81      inference('sup-', [status(thm)], ['55', '56'])).
% 49.57/49.81  thf('58', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 49.57/49.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.57/49.81  thf('59', plain,
% 49.57/49.81      (![X11 : $i, X12 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 49.57/49.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 49.57/49.81  thf('60', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 49.57/49.81      inference('sup-', [status(thm)], ['58', '59'])).
% 49.57/49.81  thf('61', plain,
% 49.57/49.81      (![X24 : $i, X25 : $i, X26 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 49.57/49.81          | ~ (r1_xboole_0 @ X24 @ X25)
% 49.57/49.81          | ~ (r1_xboole_0 @ X24 @ X26))),
% 49.57/49.81      inference('cnf', [status(esa)], [t70_xboole_1])).
% 49.57/49.81  thf('62', plain,
% 49.57/49.81      (![X0 : $i]:
% 49.57/49.81         (~ (r1_xboole_0 @ sk_B @ X0)
% 49.57/49.81          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ X0)))),
% 49.57/49.81      inference('sup-', [status(thm)], ['60', '61'])).
% 49.57/49.81  thf('63', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 49.57/49.81      inference('sup-', [status(thm)], ['57', '62'])).
% 49.57/49.81  thf('64', plain,
% 49.57/49.81      (![X11 : $i, X12 : $i]:
% 49.57/49.81         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 49.57/49.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 49.57/49.81  thf('65', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 49.57/49.81      inference('sup-', [status(thm)], ['63', '64'])).
% 49.57/49.81  thf('66', plain, ($false), inference('demod', [status(thm)], ['2', '65'])).
% 49.57/49.81  
% 49.57/49.81  % SZS output end Refutation
% 49.57/49.81  
% 49.63/49.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
