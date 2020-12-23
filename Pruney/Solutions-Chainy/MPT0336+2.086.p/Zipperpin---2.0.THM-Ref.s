%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Oqz9P6Th2Q

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:31 EST 2020

% Result     : Theorem 2.88s
% Output     : Refutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 169 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   22
%              Number of atoms          :  659 (1246 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) )
        = X28 )
      | ( r2_hidden @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
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
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
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
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
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
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('27',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['33','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('61',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('63',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('70',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['59','72'])).

thf('74',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('79',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Oqz9P6Th2Q
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.88/3.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.88/3.12  % Solved by: fo/fo7.sh
% 2.88/3.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.88/3.12  % done 6695 iterations in 2.667s
% 2.88/3.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.88/3.12  % SZS output start Refutation
% 2.88/3.12  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.88/3.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.88/3.12  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.88/3.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.88/3.12  thf(sk_B_type, type, sk_B: $i).
% 2.88/3.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.88/3.12  thf(sk_D_type, type, sk_D: $i).
% 2.88/3.12  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.88/3.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.88/3.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.88/3.12  thf(sk_A_type, type, sk_A: $i).
% 2.88/3.12  thf(t149_zfmisc_1, conjecture,
% 2.88/3.12    (![A:$i,B:$i,C:$i,D:$i]:
% 2.88/3.12     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.88/3.12         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.88/3.12       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.88/3.12  thf(zf_stmt_0, negated_conjecture,
% 2.88/3.12    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.88/3.12        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.88/3.12            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.88/3.12          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.88/3.12    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.88/3.12  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.88/3.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.12  thf('1', plain,
% 2.88/3.12      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 2.88/3.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.12  thf(commutativity_k3_xboole_0, axiom,
% 2.88/3.12    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.88/3.12  thf('2', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.88/3.12      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.88/3.12  thf('3', plain,
% 2.88/3.12      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 2.88/3.12      inference('demod', [status(thm)], ['1', '2'])).
% 2.88/3.12  thf(t65_zfmisc_1, axiom,
% 2.88/3.12    (![A:$i,B:$i]:
% 2.88/3.12     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.88/3.12       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.88/3.12  thf('4', plain,
% 2.88/3.12      (![X28 : $i, X29 : $i]:
% 2.88/3.12         (((k4_xboole_0 @ X28 @ (k1_tarski @ X29)) = (X28))
% 2.88/3.12          | (r2_hidden @ X29 @ X28))),
% 2.88/3.12      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.88/3.12  thf(t79_xboole_1, axiom,
% 2.88/3.12    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.88/3.12  thf('5', plain,
% 2.88/3.12      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 2.88/3.12      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.88/3.12  thf(symmetry_r1_xboole_0, axiom,
% 2.88/3.12    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.88/3.12  thf('6', plain,
% 2.88/3.12      (![X2 : $i, X3 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.88/3.12      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.88/3.12  thf('7', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.88/3.12      inference('sup-', [status(thm)], ['5', '6'])).
% 2.88/3.12  thf('8', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 2.88/3.12      inference('sup+', [status(thm)], ['4', '7'])).
% 2.88/3.12  thf(t70_xboole_1, axiom,
% 2.88/3.12    (![A:$i,B:$i,C:$i]:
% 2.88/3.12     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.88/3.12            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.88/3.12       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.88/3.12            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.88/3.12  thf('9', plain,
% 2.88/3.12      (![X15 : $i, X16 : $i, X18 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X15 @ X16)
% 2.88/3.12          | ~ (r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X18)))),
% 2.88/3.12      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.88/3.12  thf('10', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.12         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.88/3.12          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 2.88/3.12      inference('sup-', [status(thm)], ['8', '9'])).
% 2.88/3.12  thf('11', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.88/3.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.12  thf('12', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.88/3.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.12  thf('13', plain,
% 2.88/3.12      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 2.88/3.12          | ~ (r1_xboole_0 @ X15 @ X16)
% 2.88/3.12          | ~ (r1_xboole_0 @ X15 @ X17))),
% 2.88/3.12      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.88/3.12  thf('14', plain,
% 2.88/3.12      (![X0 : $i]:
% 2.88/3.12         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 2.88/3.12          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 2.88/3.12      inference('sup-', [status(thm)], ['12', '13'])).
% 2.88/3.12  thf('15', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 2.88/3.12      inference('sup-', [status(thm)], ['11', '14'])).
% 2.88/3.12  thf('16', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 2.88/3.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.12  thf(t3_xboole_0, axiom,
% 2.88/3.12    (![A:$i,B:$i]:
% 2.88/3.12     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.88/3.12            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.88/3.12       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.88/3.12            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.88/3.12  thf('17', plain,
% 2.88/3.12      (![X4 : $i, X6 : $i, X7 : $i]:
% 2.88/3.12         (~ (r2_hidden @ X6 @ X4)
% 2.88/3.12          | ~ (r2_hidden @ X6 @ X7)
% 2.88/3.12          | ~ (r1_xboole_0 @ X4 @ X7))),
% 2.88/3.12      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.88/3.12  thf('18', plain,
% 2.88/3.12      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 2.88/3.12      inference('sup-', [status(thm)], ['16', '17'])).
% 2.88/3.12  thf('19', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 2.88/3.12      inference('sup-', [status(thm)], ['15', '18'])).
% 2.88/3.12  thf('20', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 2.88/3.12      inference('sup-', [status(thm)], ['10', '19'])).
% 2.88/3.12  thf(t83_xboole_1, axiom,
% 2.88/3.12    (![A:$i,B:$i]:
% 2.88/3.12     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.88/3.12  thf('21', plain,
% 2.88/3.12      (![X21 : $i, X22 : $i]:
% 2.88/3.12         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 2.88/3.12      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.88/3.12  thf('22', plain,
% 2.88/3.12      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_tarski @ sk_D))),
% 2.88/3.12      inference('sup-', [status(thm)], ['20', '21'])).
% 2.88/3.12  thf(t106_xboole_1, axiom,
% 2.88/3.12    (![A:$i,B:$i,C:$i]:
% 2.88/3.12     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.88/3.12       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 2.88/3.12  thf('23', plain,
% 2.88/3.12      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X8 @ X10)
% 2.88/3.12          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.88/3.12      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.88/3.12  thf('24', plain,
% 2.88/3.12      (![X0 : $i]:
% 2.88/3.12         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 2.88/3.12      inference('sup-', [status(thm)], ['22', '23'])).
% 2.88/3.12  thf('25', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 2.88/3.12      inference('sup-', [status(thm)], ['3', '24'])).
% 2.88/3.12  thf('26', plain,
% 2.88/3.12      (![X2 : $i, X3 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.88/3.12      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.88/3.12  thf('27', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 2.88/3.12      inference('sup-', [status(thm)], ['25', '26'])).
% 2.88/3.12  thf('28', plain,
% 2.88/3.12      (![X21 : $i, X22 : $i]:
% 2.88/3.12         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 2.88/3.12      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.88/3.12  thf('29', plain,
% 2.88/3.12      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 2.88/3.12      inference('sup-', [status(thm)], ['27', '28'])).
% 2.88/3.12  thf(t48_xboole_1, axiom,
% 2.88/3.12    (![A:$i,B:$i]:
% 2.88/3.12     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.88/3.12  thf('30', plain,
% 2.88/3.12      (![X13 : $i, X14 : $i]:
% 2.88/3.12         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.88/3.12           = (k3_xboole_0 @ X13 @ X14))),
% 2.88/3.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.88/3.12  thf('31', plain,
% 2.88/3.12      (![X13 : $i, X14 : $i]:
% 2.88/3.12         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.88/3.12           = (k3_xboole_0 @ X13 @ X14))),
% 2.88/3.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.88/3.12  thf('32', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]:
% 2.88/3.12         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.88/3.12           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.88/3.12      inference('sup+', [status(thm)], ['30', '31'])).
% 2.88/3.12  thf('33', plain,
% 2.88/3.12      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 2.88/3.12      inference('demod', [status(thm)], ['29', '32'])).
% 2.88/3.12  thf('34', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.88/3.12      inference('sup-', [status(thm)], ['5', '6'])).
% 2.88/3.12  thf('35', plain,
% 2.88/3.12      (![X21 : $i, X22 : $i]:
% 2.88/3.12         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 2.88/3.12      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.88/3.12  thf('36', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]:
% 2.88/3.12         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.88/3.12      inference('sup-', [status(thm)], ['34', '35'])).
% 2.88/3.12  thf(t36_xboole_1, axiom,
% 2.88/3.12    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.88/3.12  thf('37', plain,
% 2.88/3.12      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 2.88/3.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.88/3.12  thf('38', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.88/3.12      inference('sup+', [status(thm)], ['36', '37'])).
% 2.88/3.12  thf('39', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.88/3.12      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.88/3.12  thf('40', plain,
% 2.88/3.12      (![X13 : $i, X14 : $i]:
% 2.88/3.12         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.88/3.12           = (k3_xboole_0 @ X13 @ X14))),
% 2.88/3.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.88/3.12  thf('41', plain,
% 2.88/3.12      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.88/3.12         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.88/3.12      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.88/3.12  thf('42', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.12         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 2.88/3.12      inference('sup-', [status(thm)], ['40', '41'])).
% 2.88/3.12  thf('43', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.12         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 2.88/3.12      inference('sup-', [status(thm)], ['39', '42'])).
% 2.88/3.12  thf('44', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.88/3.12      inference('sup-', [status(thm)], ['38', '43'])).
% 2.88/3.12  thf('45', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))),
% 2.88/3.12      inference('sup+', [status(thm)], ['33', '44'])).
% 2.88/3.12  thf('46', plain,
% 2.88/3.12      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X8 @ X10)
% 2.88/3.12          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.88/3.12      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.88/3.12  thf('47', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.88/3.12      inference('sup-', [status(thm)], ['45', '46'])).
% 2.88/3.12  thf('48', plain,
% 2.88/3.12      (![X21 : $i, X22 : $i]:
% 2.88/3.12         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 2.88/3.12      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.88/3.12  thf('49', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.88/3.12      inference('sup-', [status(thm)], ['47', '48'])).
% 2.88/3.12  thf('50', plain,
% 2.88/3.12      (![X13 : $i, X14 : $i]:
% 2.88/3.12         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.88/3.12           = (k3_xboole_0 @ X13 @ X14))),
% 2.88/3.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.88/3.12  thf('51', plain,
% 2.88/3.12      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 2.88/3.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.88/3.12  thf('52', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.88/3.12      inference('sup+', [status(thm)], ['50', '51'])).
% 2.88/3.12  thf('53', plain,
% 2.88/3.12      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X8 @ X10)
% 2.88/3.12          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.88/3.12      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.88/3.12  thf('54', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.12         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 2.88/3.12      inference('sup-', [status(thm)], ['52', '53'])).
% 2.88/3.12  thf('55', plain,
% 2.88/3.12      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 2.88/3.12      inference('sup+', [status(thm)], ['49', '54'])).
% 2.88/3.12  thf('56', plain,
% 2.88/3.12      (![X2 : $i, X3 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.88/3.12      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.88/3.12  thf('57', plain,
% 2.88/3.12      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))),
% 2.88/3.12      inference('sup-', [status(thm)], ['55', '56'])).
% 2.88/3.12  thf('58', plain,
% 2.88/3.12      (![X21 : $i, X22 : $i]:
% 2.88/3.12         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 2.88/3.12      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.88/3.12  thf('59', plain,
% 2.88/3.12      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) = (sk_A))),
% 2.88/3.12      inference('sup-', [status(thm)], ['57', '58'])).
% 2.88/3.12  thf('60', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.88/3.12      inference('sup-', [status(thm)], ['38', '43'])).
% 2.88/3.12  thf('61', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.88/3.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.12  thf('62', plain,
% 2.88/3.12      (![X2 : $i, X3 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.88/3.12      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.88/3.12  thf('63', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.88/3.12      inference('sup-', [status(thm)], ['61', '62'])).
% 2.88/3.12  thf('64', plain,
% 2.88/3.12      (![X21 : $i, X22 : $i]:
% 2.88/3.12         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 2.88/3.12      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.88/3.12  thf('65', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 2.88/3.12      inference('sup-', [status(thm)], ['63', '64'])).
% 2.88/3.12  thf('66', plain,
% 2.88/3.12      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X8 @ X10)
% 2.88/3.12          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.88/3.12      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.88/3.12  thf('67', plain,
% 2.88/3.12      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_C_1))),
% 2.88/3.12      inference('sup-', [status(thm)], ['65', '66'])).
% 2.88/3.12  thf('68', plain,
% 2.88/3.12      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_C_1)),
% 2.88/3.12      inference('sup-', [status(thm)], ['60', '67'])).
% 2.88/3.12  thf('69', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.88/3.12      inference('sup-', [status(thm)], ['5', '6'])).
% 2.88/3.12  thf('70', plain,
% 2.88/3.12      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 2.88/3.12          | ~ (r1_xboole_0 @ X15 @ X16)
% 2.88/3.12          | ~ (r1_xboole_0 @ X15 @ X17))),
% 2.88/3.12      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.88/3.12  thf('71', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.12         (~ (r1_xboole_0 @ X0 @ X2)
% 2.88/3.12          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 2.88/3.12      inference('sup-', [status(thm)], ['69', '70'])).
% 2.88/3.12  thf('72', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]:
% 2.88/3.12         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 2.88/3.12          (k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 2.88/3.12           sk_C_1))),
% 2.88/3.12      inference('sup-', [status(thm)], ['68', '71'])).
% 2.88/3.12  thf('73', plain,
% 2.88/3.12      ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_B) @ 
% 2.88/3.12        (k2_xboole_0 @ sk_A @ sk_C_1))),
% 2.88/3.12      inference('sup+', [status(thm)], ['59', '72'])).
% 2.88/3.12  thf('74', plain,
% 2.88/3.12      (![X13 : $i, X14 : $i]:
% 2.88/3.12         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.88/3.12           = (k3_xboole_0 @ X13 @ X14))),
% 2.88/3.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.88/3.12  thf('75', plain,
% 2.88/3.12      (![X0 : $i, X1 : $i]:
% 2.88/3.12         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.88/3.12      inference('sup-', [status(thm)], ['34', '35'])).
% 2.88/3.12  thf('76', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.88/3.12      inference('sup+', [status(thm)], ['74', '75'])).
% 2.88/3.12  thf('77', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 2.88/3.12      inference('demod', [status(thm)], ['73', '76'])).
% 2.88/3.12  thf('78', plain,
% 2.88/3.12      (![X2 : $i, X3 : $i]:
% 2.88/3.12         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.88/3.12      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.88/3.12  thf('79', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.88/3.12      inference('sup-', [status(thm)], ['77', '78'])).
% 2.88/3.12  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 2.88/3.12  
% 2.88/3.12  % SZS output end Refutation
% 2.88/3.12  
% 2.88/3.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
