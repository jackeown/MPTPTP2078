%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5SIpDN8KXS

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:32 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 171 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  599 (1294 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('1',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k4_xboole_0 @ X32 @ ( k1_tarski @ X33 ) )
        = X32 )
      | ( r2_hidden @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ( r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
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

thf('17',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['10','19'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ ( k3_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X2 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('47',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('56',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup+',[status(thm)],['53','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5SIpDN8KXS
% 0.16/0.37  % Computer   : n012.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 18:59:07 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.72/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.92  % Solved by: fo/fo7.sh
% 0.72/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.92  % done 1240 iterations in 0.442s
% 0.72/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.92  % SZS output start Refutation
% 0.72/0.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.92  thf(sk_D_type, type, sk_D: $i).
% 0.72/0.92  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.72/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.72/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.92  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.72/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.92  thf(t149_zfmisc_1, conjecture,
% 0.72/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.92     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.72/0.92         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.72/0.92       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.72/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.92    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.92        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.72/0.92            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.72/0.92          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.72/0.92    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.72/0.92  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('1', plain,
% 0.72/0.92      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(commutativity_k3_xboole_0, axiom,
% 0.72/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.72/0.92  thf('2', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.92  thf('3', plain,
% 0.72/0.92      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.72/0.92      inference('demod', [status(thm)], ['1', '2'])).
% 0.72/0.92  thf(t65_zfmisc_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.72/0.92       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.72/0.92  thf('4', plain,
% 0.72/0.92      (![X32 : $i, X33 : $i]:
% 0.72/0.92         (((k4_xboole_0 @ X32 @ (k1_tarski @ X33)) = (X32))
% 0.72/0.92          | (r2_hidden @ X33 @ X32))),
% 0.72/0.92      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.72/0.92  thf(t79_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.72/0.92  thf('5', plain,
% 0.72/0.92      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.72/0.92      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.72/0.92  thf(symmetry_r1_xboole_0, axiom,
% 0.72/0.92    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.72/0.92  thf('6', plain,
% 0.72/0.92      (![X2 : $i, X3 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.72/0.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.72/0.92  thf('7', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.72/0.92  thf('8', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 0.72/0.92      inference('sup+', [status(thm)], ['4', '7'])).
% 0.72/0.92  thf(t70_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.72/0.92            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.72/0.92       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.72/0.92            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.72/0.92  thf('9', plain,
% 0.72/0.92      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X14 @ X15)
% 0.72/0.92          | ~ (r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X17)))),
% 0.72/0.92      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.72/0.92  thf('10', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.72/0.92          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['8', '9'])).
% 0.72/0.92  thf('11', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('12', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('13', plain,
% 0.72/0.92      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.72/0.92          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.72/0.92          | ~ (r1_xboole_0 @ X14 @ X16))),
% 0.72/0.92      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.72/0.92  thf('14', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (r1_xboole_0 @ sk_C_2 @ X0)
% 0.72/0.92          | (r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['12', '13'])).
% 0.72/0.92  thf('15', plain, ((r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.72/0.92      inference('sup-', [status(thm)], ['11', '14'])).
% 0.72/0.92  thf('16', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(t3_xboole_0, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.72/0.92            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.92       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.72/0.92            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.72/0.92  thf('17', plain,
% 0.72/0.92      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X6 @ X4)
% 0.72/0.92          | ~ (r2_hidden @ X6 @ X7)
% 0.72/0.92          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.72/0.92      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.72/0.92  thf('18', plain,
% 0.72/0.92      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['16', '17'])).
% 0.72/0.92  thf('19', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.72/0.92      inference('sup-', [status(thm)], ['15', '18'])).
% 0.72/0.92  thf('20', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 0.72/0.92      inference('sup-', [status(thm)], ['10', '19'])).
% 0.72/0.92  thf(t83_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.72/0.92  thf('21', plain,
% 0.72/0.92      (![X25 : $i, X26 : $i]:
% 0.72/0.92         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.72/0.92      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.72/0.92  thf('22', plain,
% 0.72/0.92      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_tarski @ sk_D))),
% 0.72/0.92      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.92  thf('23', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.72/0.92  thf('24', plain,
% 0.72/0.92      (![X25 : $i, X26 : $i]:
% 0.72/0.92         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.72/0.92      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.72/0.92  thf('25', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['23', '24'])).
% 0.72/0.92  thf(t48_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.72/0.92  thf('26', plain,
% 0.72/0.92      (![X12 : $i, X13 : $i]:
% 0.72/0.92         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.72/0.92           = (k3_xboole_0 @ X12 @ X13))),
% 0.72/0.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.72/0.92  thf('27', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((k4_xboole_0 @ X0 @ X0)
% 0.72/0.92           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.92      inference('sup+', [status(thm)], ['25', '26'])).
% 0.72/0.92  thf('28', plain,
% 0.72/0.92      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.72/0.92      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.72/0.92  thf(t77_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.72/0.92          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.72/0.92  thf('29', plain,
% 0.72/0.92      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X20 @ X21)
% 0.72/0.92          | ~ (r1_xboole_0 @ X20 @ (k3_xboole_0 @ X21 @ X22))
% 0.72/0.92          | ~ (r1_tarski @ X20 @ X22))),
% 0.72/0.92      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.72/0.92  thf('30', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         (~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 0.72/0.92          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['28', '29'])).
% 0.72/0.92  thf('31', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         (~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X0)) @ 
% 0.72/0.92             (k4_xboole_0 @ X1 @ X0))
% 0.72/0.92          | (r1_xboole_0 @ 
% 0.72/0.92             (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 0.72/0.92             X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['27', '30'])).
% 0.72/0.92  thf('32', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.72/0.92  thf('33', plain,
% 0.72/0.92      (![X4 : $i, X5 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.72/0.92      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.72/0.92  thf(t4_xboole_0, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.92            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.72/0.92       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.72/0.92            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.72/0.92  thf('34', plain,
% 0.72/0.92      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.72/0.92          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.72/0.92      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.72/0.92  thf('35', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.72/0.92          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['33', '34'])).
% 0.72/0.92  thf('36', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)),
% 0.72/0.92      inference('sup-', [status(thm)], ['32', '35'])).
% 0.72/0.92  thf('37', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((k4_xboole_0 @ X0 @ X0)
% 0.72/0.92           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.92      inference('sup+', [status(thm)], ['25', '26'])).
% 0.72/0.92  thf('38', plain,
% 0.72/0.92      (![X0 : $i, X2 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X2)),
% 0.72/0.92      inference('demod', [status(thm)], ['36', '37'])).
% 0.72/0.92  thf('39', plain,
% 0.72/0.92      (![X2 : $i, X3 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.72/0.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.72/0.92  thf('40', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['38', '39'])).
% 0.72/0.92  thf('41', plain,
% 0.72/0.92      (![X25 : $i, X26 : $i]:
% 0.72/0.92         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.72/0.92      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.72/0.92  thf('42', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['40', '41'])).
% 0.72/0.92  thf('43', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((k4_xboole_0 @ X0 @ X0)
% 0.72/0.92           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.72/0.92      inference('sup+', [status(thm)], ['25', '26'])).
% 0.72/0.92  thf('44', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['40', '41'])).
% 0.72/0.92  thf('45', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.72/0.92          | (r1_xboole_0 @ X2 @ X0))),
% 0.72/0.92      inference('demod', [status(thm)], ['31', '42', '43', '44'])).
% 0.72/0.92  thf('46', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.72/0.92      inference('sup-', [status(thm)], ['22', '45'])).
% 0.72/0.92  thf('47', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.72/0.92      inference('sup-', [status(thm)], ['3', '46'])).
% 0.72/0.92  thf('48', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.92  thf(t75_xboole_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.72/0.92          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.72/0.92  thf('49', plain,
% 0.72/0.92      (![X18 : $i, X19 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X18 @ X19)
% 0.72/0.92          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X19))),
% 0.72/0.92      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.72/0.92  thf('50', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.72/0.92          | (r1_xboole_0 @ X0 @ X1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['48', '49'])).
% 0.72/0.92  thf('51', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.72/0.92      inference('sup-', [status(thm)], ['47', '50'])).
% 0.72/0.92  thf('52', plain,
% 0.72/0.92      (![X25 : $i, X26 : $i]:
% 0.72/0.92         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 0.72/0.92      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.72/0.92  thf('53', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.72/0.92      inference('sup-', [status(thm)], ['51', '52'])).
% 0.72/0.92  thf('54', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('55', plain,
% 0.72/0.92      (![X2 : $i, X3 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.72/0.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.72/0.92  thf('56', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.72/0.92      inference('sup-', [status(thm)], ['54', '55'])).
% 0.72/0.92  thf('57', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.72/0.92  thf('58', plain,
% 0.72/0.92      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.72/0.92         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.72/0.92          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.72/0.92          | ~ (r1_xboole_0 @ X14 @ X16))),
% 0.72/0.92      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.72/0.92  thf('59', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         (~ (r1_xboole_0 @ X0 @ X2)
% 0.72/0.92          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['57', '58'])).
% 0.72/0.93  thf('60', plain,
% 0.72/0.93      (![X0 : $i]:
% 0.72/0.93         (r1_xboole_0 @ sk_B @ 
% 0.72/0.93          (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C_2))),
% 0.72/0.93      inference('sup-', [status(thm)], ['56', '59'])).
% 0.72/0.93  thf('61', plain,
% 0.72/0.93      (![X2 : $i, X3 : $i]:
% 0.72/0.93         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.72/0.93      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.72/0.93  thf('62', plain,
% 0.72/0.93      (![X0 : $i]:
% 0.72/0.93         (r1_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C_2) @ 
% 0.72/0.93          sk_B)),
% 0.72/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.72/0.93  thf('63', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.72/0.93      inference('sup+', [status(thm)], ['53', '62'])).
% 0.72/0.93  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.72/0.93  
% 0.72/0.93  % SZS output end Refutation
% 0.72/0.93  
% 0.72/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
