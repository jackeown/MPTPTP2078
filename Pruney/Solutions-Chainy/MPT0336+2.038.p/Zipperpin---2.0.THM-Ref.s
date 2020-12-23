%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nzqbOk1sWl

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:25 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 133 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  740 (1244 expanded)
%              Number of equality atoms :   29 (  42 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_3 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
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
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
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

thf('10',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('12',plain,(
    r2_hidden @ sk_D_1 @ sk_C_3 ),
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

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( X27 = X24 )
      | ( X26
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X24: $i,X27: $i] :
      ( ( X27 = X24 )
      | ~ ( r2_hidden @ X27 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['10','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','62'])).

thf('64',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['47','63'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('65',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['3','66'])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('69',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_3 ) @ sk_B ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nzqbOk1sWl
% 0.15/0.36  % Computer   : n015.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 09:42:08 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.78/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/0.97  % Solved by: fo/fo7.sh
% 0.78/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.97  % done 976 iterations in 0.490s
% 0.78/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/0.97  % SZS output start Refutation
% 0.78/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.78/0.97  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.78/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.78/0.97  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.78/0.97  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.78/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.78/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.78/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.97  thf(t149_zfmisc_1, conjecture,
% 0.78/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.97     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.78/0.97         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.78/0.97       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.78/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.97    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.97        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.78/0.97            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.78/0.97          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.78/0.97    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.78/0.97  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_3) @ sk_B)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('1', plain, ((r1_xboole_0 @ sk_C_3 @ sk_B)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(symmetry_r1_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.78/0.97  thf('2', plain,
% 0.78/0.97      (![X8 : $i, X9 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.78/0.97      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.78/0.97  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_3)),
% 0.78/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.78/0.97  thf('4', plain,
% 0.78/0.97      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.78/0.97  thf('5', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.97  thf('6', plain,
% 0.78/0.97      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.78/0.97      inference('demod', [status(thm)], ['4', '5'])).
% 0.78/0.97  thf(t28_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.78/0.97  thf('7', plain,
% 0.78/0.97      (![X18 : $i, X19 : $i]:
% 0.78/0.97         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.78/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/0.97  thf('8', plain,
% 0.78/0.97      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 0.78/0.97         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.78/0.97      inference('sup-', [status(thm)], ['6', '7'])).
% 0.78/0.97  thf('9', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.97  thf('10', plain,
% 0.78/0.97      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.78/0.97         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.78/0.97      inference('demod', [status(thm)], ['8', '9'])).
% 0.78/0.97  thf('11', plain, ((r1_xboole_0 @ sk_B @ sk_C_3)),
% 0.78/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.78/0.97  thf('12', plain, ((r2_hidden @ sk_D_1 @ sk_C_3)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(t3_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.78/0.97            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.78/0.97       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.78/0.97            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.78/0.97  thf('13', plain,
% 0.78/0.97      (![X10 : $i, X11 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 0.78/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.97  thf(d1_tarski, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.78/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.78/0.97  thf('14', plain,
% 0.78/0.97      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X27 @ X26)
% 0.78/0.97          | ((X27) = (X24))
% 0.78/0.97          | ((X26) != (k1_tarski @ X24)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d1_tarski])).
% 0.78/0.97  thf('15', plain,
% 0.78/0.97      (![X24 : $i, X27 : $i]:
% 0.78/0.97         (((X27) = (X24)) | ~ (r2_hidden @ X27 @ (k1_tarski @ X24)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['14'])).
% 0.78/0.97  thf('16', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.78/0.97          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['13', '15'])).
% 0.78/0.97  thf('17', plain,
% 0.78/0.97      (![X10 : $i, X11 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X11))),
% 0.78/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.97  thf('18', plain,
% 0.78/0.97      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X12 @ X10)
% 0.78/0.97          | ~ (r2_hidden @ X12 @ X13)
% 0.78/0.97          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.78/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.97  thf('19', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X1 @ X0)
% 0.78/0.97          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.78/0.97          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.78/0.97      inference('sup-', [status(thm)], ['17', '18'])).
% 0.78/0.97  thf('20', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X0 @ X1)
% 0.78/0.97          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 0.78/0.97          | ~ (r1_xboole_0 @ X2 @ X1)
% 0.78/0.97          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2))),
% 0.78/0.97      inference('sup-', [status(thm)], ['16', '19'])).
% 0.78/0.97  thf('21', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (~ (r1_xboole_0 @ X2 @ X1)
% 0.78/0.97          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 0.78/0.97          | ~ (r2_hidden @ X0 @ X1))),
% 0.78/0.97      inference('simplify', [status(thm)], ['20'])).
% 0.78/0.97  thf('22', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)
% 0.78/0.97          | ~ (r1_xboole_0 @ X0 @ sk_C_3))),
% 0.78/0.97      inference('sup-', [status(thm)], ['12', '21'])).
% 0.78/0.97  thf('23', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_B)),
% 0.78/0.97      inference('sup-', [status(thm)], ['11', '22'])).
% 0.78/0.97  thf('24', plain,
% 0.78/0.97      (![X8 : $i, X9 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.78/0.97      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.78/0.97  thf('25', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['23', '24'])).
% 0.78/0.97  thf('26', plain,
% 0.78/0.97      (![X10 : $i, X11 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X11))),
% 0.78/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.97  thf('27', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.97  thf(d4_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i,C:$i]:
% 0.78/0.97     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.78/0.97       ( ![D:$i]:
% 0.78/0.97         ( ( r2_hidden @ D @ C ) <=>
% 0.78/0.97           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.78/0.97  thf('28', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X6 @ X5)
% 0.78/0.97          | (r2_hidden @ X6 @ X4)
% 0.78/0.97          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.78/0.97  thf('29', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.78/0.97         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['28'])).
% 0.78/0.97  thf('30', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['27', '29'])).
% 0.78/0.97  thf('31', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.78/0.97          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['26', '30'])).
% 0.78/0.97  thf('32', plain,
% 0.78/0.97      (![X10 : $i, X11 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 0.78/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.97  thf('33', plain,
% 0.78/0.97      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X12 @ X10)
% 0.78/0.97          | ~ (r2_hidden @ X12 @ X13)
% 0.78/0.97          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.78/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.97  thf('34', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X0 @ X1)
% 0.78/0.97          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.78/0.97          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.78/0.97      inference('sup-', [status(thm)], ['32', '33'])).
% 0.78/0.97  thf('35', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))
% 0.78/0.97          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.78/0.97          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['31', '34'])).
% 0.78/0.97  thf('36', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (~ (r1_xboole_0 @ X1 @ X0)
% 0.78/0.97          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['35'])).
% 0.78/0.97  thf('37', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['25', '36'])).
% 0.78/0.97  thf('38', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.78/0.97      inference('sup+', [status(thm)], ['10', '37'])).
% 0.78/0.97  thf('39', plain,
% 0.78/0.97      (![X8 : $i, X9 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.78/0.97      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.78/0.97  thf('40', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.78/0.97      inference('sup-', [status(thm)], ['38', '39'])).
% 0.78/0.97  thf('41', plain,
% 0.78/0.97      (![X10 : $i, X11 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 0.78/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.97  thf('42', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['27', '29'])).
% 0.78/0.97  thf('43', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.78/0.97          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['41', '42'])).
% 0.78/0.97  thf('44', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X0 @ X1)
% 0.78/0.97          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.78/0.97          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.78/0.97      inference('sup-', [status(thm)], ['32', '33'])).
% 0.78/0.97  thf('45', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.78/0.97          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.78/0.97          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 0.78/0.97      inference('sup-', [status(thm)], ['43', '44'])).
% 0.78/0.97  thf('46', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.78/0.97          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 0.78/0.97      inference('simplify', [status(thm)], ['45'])).
% 0.78/0.97  thf('47', plain,
% 0.78/0.97      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)),
% 0.78/0.97      inference('sup-', [status(thm)], ['40', '46'])).
% 0.78/0.97  thf(t4_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.78/0.97            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.78/0.97       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.78/0.97            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.78/0.97  thf('48', plain,
% 0.78/0.97      (![X14 : $i, X15 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X14 @ X15)
% 0.78/0.97          | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ (k3_xboole_0 @ X14 @ X15)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.78/0.97  thf('49', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.78/0.97         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.78/0.97          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.78/0.97          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.78/0.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.78/0.97  thf('50', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.78/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('eq_fact', [status(thm)], ['49'])).
% 0.78/0.97  thf('51', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.78/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('eq_fact', [status(thm)], ['49'])).
% 0.78/0.97  thf('52', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.78/0.97         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.78/0.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.78/0.97  thf('53', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.78/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['51', '52'])).
% 0.78/0.97  thf('54', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.78/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['53'])).
% 0.78/0.97  thf('55', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.78/0.97          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('eq_fact', [status(thm)], ['49'])).
% 0.78/0.97  thf('56', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.78/0.97          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.78/0.97      inference('clc', [status(thm)], ['54', '55'])).
% 0.78/0.97  thf('57', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['50', '56'])).
% 0.78/0.97  thf('58', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.78/0.97      inference('simplify', [status(thm)], ['57'])).
% 0.78/0.97  thf('59', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.97  thf('60', plain,
% 0.78/0.97      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 0.78/0.97          | ~ (r1_xboole_0 @ X14 @ X17))),
% 0.78/0.97      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.78/0.97  thf('61', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.78/0.97          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['59', '60'])).
% 0.78/0.97  thf('62', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['58', '61'])).
% 0.78/0.97  thf('63', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X1 @ X0)
% 0.78/0.97          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['48', '62'])).
% 0.78/0.97  thf('64', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.78/0.97      inference('sup-', [status(thm)], ['47', '63'])).
% 0.78/0.97  thf(t70_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i,C:$i]:
% 0.78/0.97     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.78/0.97            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.78/0.97       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.78/0.97            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.78/0.97  thf('65', plain,
% 0.78/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 0.78/0.97          | ~ (r1_xboole_0 @ X20 @ X21)
% 0.78/0.97          | ~ (r1_xboole_0 @ X20 @ X22))),
% 0.78/0.97      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.78/0.97  thf('66', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.78/0.97          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['64', '65'])).
% 0.78/0.97  thf('67', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_3))),
% 0.78/0.97      inference('sup-', [status(thm)], ['3', '66'])).
% 0.78/0.97  thf('68', plain,
% 0.78/0.97      (![X8 : $i, X9 : $i]:
% 0.78/0.97         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 0.78/0.97      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.78/0.97  thf('69', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_3) @ sk_B)),
% 0.78/0.97      inference('sup-', [status(thm)], ['67', '68'])).
% 0.78/0.97  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 0.78/0.97  
% 0.78/0.97  % SZS output end Refutation
% 0.78/0.97  
% 0.78/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
