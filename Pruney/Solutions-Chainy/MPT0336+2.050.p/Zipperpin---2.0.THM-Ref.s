%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fHpnYN3HKf

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:26 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 335 expanded)
%              Number of leaves         :   24 ( 115 expanded)
%              Depth                    :   25
%              Number of atoms          :  803 (2844 expanded)
%              Number of equality atoms :   35 ( 115 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('23',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
      | ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf('51',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['33','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('53',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['22','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('62',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('70',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['74','75','76','79'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('81',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( ( k3_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
        = ( k3_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('87',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('93',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['19','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['0','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fHpnYN3HKf
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.50/1.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.70  % Solved by: fo/fo7.sh
% 1.50/1.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.70  % done 3933 iterations in 1.241s
% 1.50/1.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.70  % SZS output start Refutation
% 1.50/1.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.50/1.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.50/1.70  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.70  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.50/1.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.50/1.70  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.50/1.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.50/1.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.50/1.70  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.50/1.70  thf(sk_D_type, type, sk_D: $i).
% 1.50/1.70  thf(t149_zfmisc_1, conjecture,
% 1.50/1.70    (![A:$i,B:$i,C:$i,D:$i]:
% 1.50/1.70     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.50/1.70         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.50/1.70       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.50/1.70  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.50/1.70        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.50/1.70            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.50/1.70          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.50/1.70    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.50/1.70  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf(commutativity_k3_xboole_0, axiom,
% 1.50/1.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.50/1.70  thf('1', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf(t17_xboole_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.50/1.70  thf('2', plain,
% 1.50/1.70      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 1.50/1.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.50/1.70  thf('3', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.50/1.70      inference('sup+', [status(thm)], ['1', '2'])).
% 1.50/1.70  thf('4', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf(d7_xboole_0, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.50/1.70       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.50/1.70  thf('5', plain,
% 1.50/1.70      (![X2 : $i, X3 : $i]:
% 1.50/1.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.50/1.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.50/1.70  thf('6', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['4', '5'])).
% 1.50/1.70  thf('7', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('8', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 1.50/1.70      inference('demod', [status(thm)], ['6', '7'])).
% 1.50/1.70  thf(t77_xboole_1, axiom,
% 1.50/1.70    (![A:$i,B:$i,C:$i]:
% 1.50/1.70     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 1.50/1.70          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 1.50/1.70  thf('9', plain,
% 1.50/1.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X19 @ X20)
% 1.50/1.70          | ~ (r1_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21))
% 1.50/1.70          | ~ (r1_tarski @ X19 @ X21))),
% 1.50/1.70      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.50/1.70  thf('10', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.50/1.70          | ~ (r1_tarski @ X0 @ sk_C_2)
% 1.50/1.70          | (r1_xboole_0 @ X0 @ sk_B))),
% 1.50/1.70      inference('sup-', [status(thm)], ['8', '9'])).
% 1.50/1.70  thf(t3_xboole_0, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.50/1.70            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.50/1.70       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.50/1.70            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.50/1.70  thf('11', plain,
% 1.50/1.70      (![X7 : $i, X8 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X8))),
% 1.50/1.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.50/1.70  thf('12', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['4', '5'])).
% 1.50/1.70  thf(t4_xboole_0, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.50/1.70            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.50/1.70       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.50/1.70            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.50/1.70  thf('13', plain,
% 1.50/1.70      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 1.50/1.70          | ~ (r1_xboole_0 @ X11 @ X14))),
% 1.50/1.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.50/1.70  thf('14', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_C_2 @ sk_B))),
% 1.50/1.70      inference('sup-', [status(thm)], ['12', '13'])).
% 1.50/1.70  thf('15', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.50/1.70      inference('demod', [status(thm)], ['14', '15'])).
% 1.50/1.70  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.50/1.70      inference('sup-', [status(thm)], ['11', '16'])).
% 1.50/1.70  thf('18', plain,
% 1.50/1.70      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_2) | (r1_xboole_0 @ X0 @ sk_B))),
% 1.50/1.70      inference('demod', [status(thm)], ['10', '17'])).
% 1.50/1.70  thf('19', plain,
% 1.50/1.70      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_2) @ sk_B)),
% 1.50/1.70      inference('sup-', [status(thm)], ['3', '18'])).
% 1.50/1.70  thf('20', plain,
% 1.50/1.70      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('21', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('22', plain,
% 1.50/1.70      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.50/1.70      inference('demod', [status(thm)], ['20', '21'])).
% 1.50/1.70  thf(l27_zfmisc_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.50/1.70  thf('23', plain,
% 1.50/1.70      (![X53 : $i, X54 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ (k1_tarski @ X53) @ X54) | (r2_hidden @ X53 @ X54))),
% 1.50/1.70      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.50/1.70  thf('24', plain,
% 1.50/1.70      (![X11 : $i, X12 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X11 @ X12)
% 1.50/1.70          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 1.50/1.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.50/1.70  thf('25', plain,
% 1.50/1.70      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 1.50/1.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.50/1.70  thf(t28_xboole_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.50/1.70  thf('26', plain,
% 1.50/1.70      (![X17 : $i, X18 : $i]:
% 1.50/1.70         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 1.50/1.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.50/1.70  thf('27', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.50/1.70           = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('sup-', [status(thm)], ['25', '26'])).
% 1.50/1.70  thf('28', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('29', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.50/1.70           = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('demod', [status(thm)], ['27', '28'])).
% 1.50/1.70  thf('30', plain,
% 1.50/1.70      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 1.50/1.70          | ~ (r1_xboole_0 @ X11 @ X14))),
% 1.50/1.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.50/1.70  thf('31', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.70          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.50/1.70      inference('sup-', [status(thm)], ['29', '30'])).
% 1.50/1.70  thf('32', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X1 @ X0)
% 1.50/1.70          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.50/1.70      inference('sup-', [status(thm)], ['24', '31'])).
% 1.50/1.70  thf('33', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.50/1.70          | (r1_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['23', '32'])).
% 1.50/1.70  thf('34', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('35', plain,
% 1.50/1.70      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 1.50/1.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.50/1.70  thf('36', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 1.50/1.70      inference('demod', [status(thm)], ['6', '7'])).
% 1.50/1.70  thf('37', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('38', plain,
% 1.50/1.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X19 @ X20)
% 1.50/1.70          | ~ (r1_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21))
% 1.50/1.70          | ~ (r1_tarski @ X19 @ X21))),
% 1.50/1.70      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.50/1.70  thf('39', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.70          | ~ (r1_tarski @ X2 @ X1)
% 1.50/1.70          | (r1_xboole_0 @ X2 @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['37', '38'])).
% 1.50/1.70  thf('40', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.50/1.70          | (r1_xboole_0 @ X0 @ sk_C_2)
% 1.50/1.70          | ~ (r1_tarski @ X0 @ sk_B))),
% 1.50/1.70      inference('sup-', [status(thm)], ['36', '39'])).
% 1.50/1.70  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.50/1.70      inference('sup-', [status(thm)], ['11', '16'])).
% 1.50/1.70  thf('42', plain,
% 1.50/1.70      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C_2) | ~ (r1_tarski @ X0 @ sk_B))),
% 1.50/1.70      inference('demod', [status(thm)], ['40', '41'])).
% 1.50/1.70  thf('43', plain,
% 1.50/1.70      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_2)),
% 1.50/1.70      inference('sup-', [status(thm)], ['35', '42'])).
% 1.50/1.70  thf(symmetry_r1_xboole_0, axiom,
% 1.50/1.70    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.50/1.70  thf('44', plain,
% 1.50/1.70      (![X5 : $i, X6 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.50/1.70      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.50/1.70  thf('45', plain,
% 1.50/1.70      (![X0 : $i]: (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ sk_B @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['43', '44'])).
% 1.50/1.70  thf('46', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('47', plain,
% 1.50/1.70      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X9 @ X7)
% 1.50/1.70          | ~ (r2_hidden @ X9 @ X10)
% 1.50/1.70          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.50/1.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.50/1.70  thf('48', plain,
% 1.50/1.70      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['46', '47'])).
% 1.50/1.70  thf('49', plain,
% 1.50/1.70      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['45', '48'])).
% 1.50/1.70  thf('50', plain,
% 1.50/1.70      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.50/1.70      inference('sup-', [status(thm)], ['34', '49'])).
% 1.50/1.70  thf('51', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 1.50/1.70      inference('sup-', [status(thm)], ['33', '50'])).
% 1.50/1.70  thf('52', plain,
% 1.50/1.70      (![X2 : $i, X3 : $i]:
% 1.50/1.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.50/1.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.50/1.70  thf('53', plain,
% 1.50/1.70      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_xboole_0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['51', '52'])).
% 1.50/1.70  thf('54', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('55', plain,
% 1.50/1.70      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 1.50/1.70      inference('demod', [status(thm)], ['53', '54'])).
% 1.50/1.70  thf('56', plain,
% 1.50/1.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X19 @ X20)
% 1.50/1.70          | ~ (r1_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21))
% 1.50/1.70          | ~ (r1_tarski @ X19 @ X21))),
% 1.50/1.70      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.50/1.70  thf('57', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.50/1.70          | ~ (r1_tarski @ X0 @ (k1_tarski @ sk_D))
% 1.50/1.70          | (r1_xboole_0 @ X0 @ sk_B))),
% 1.50/1.70      inference('sup-', [status(thm)], ['55', '56'])).
% 1.50/1.70  thf('58', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.50/1.70      inference('sup-', [status(thm)], ['11', '16'])).
% 1.50/1.70  thf('59', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 1.50/1.70      inference('demod', [status(thm)], ['57', '58'])).
% 1.50/1.70  thf('60', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 1.50/1.70      inference('sup-', [status(thm)], ['22', '59'])).
% 1.50/1.70  thf('61', plain,
% 1.50/1.70      (![X2 : $i, X3 : $i]:
% 1.50/1.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.50/1.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.50/1.70  thf('62', plain,
% 1.50/1.70      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['60', '61'])).
% 1.50/1.70  thf('63', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('64', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.50/1.70           = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('demod', [status(thm)], ['27', '28'])).
% 1.50/1.70  thf('65', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.50/1.70      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.50/1.70  thf('66', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('67', plain,
% 1.50/1.70      (![X11 : $i, X12 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X11 @ X12)
% 1.50/1.70          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 1.50/1.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.50/1.70  thf('68', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.70          | (r1_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('sup+', [status(thm)], ['66', '67'])).
% 1.50/1.70  thf('69', plain,
% 1.50/1.70      (![X11 : $i, X12 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X11 @ X12)
% 1.50/1.70          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 1.50/1.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.50/1.70  thf('70', plain,
% 1.50/1.70      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X9 @ X7)
% 1.50/1.70          | ~ (r2_hidden @ X9 @ X10)
% 1.50/1.70          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.50/1.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.50/1.70  thf('71', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X1 @ X0)
% 1.50/1.70          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.50/1.70          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 1.50/1.70      inference('sup-', [status(thm)], ['69', '70'])).
% 1.50/1.70  thf('72', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X0 @ X1)
% 1.50/1.70          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.70          | (r1_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('sup-', [status(thm)], ['68', '71'])).
% 1.50/1.70  thf('73', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.70          | (r1_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('simplify', [status(thm)], ['72'])).
% 1.50/1.70  thf('74', plain,
% 1.50/1.70      ((~ (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))
% 1.50/1.70        | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.50/1.70      inference('sup-', [status(thm)], ['65', '73'])).
% 1.50/1.70  thf('75', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('76', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.50/1.70      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.50/1.70  thf('77', plain,
% 1.50/1.70      (![X7 : $i, X8 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 1.50/1.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.50/1.70  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.50/1.70      inference('demod', [status(thm)], ['14', '15'])).
% 1.50/1.70  thf('79', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.50/1.70      inference('sup-', [status(thm)], ['77', '78'])).
% 1.50/1.70  thf('80', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.50/1.70      inference('demod', [status(thm)], ['74', '75', '76', '79'])).
% 1.50/1.70  thf(t78_xboole_1, axiom,
% 1.50/1.70    (![A:$i,B:$i,C:$i]:
% 1.50/1.70     ( ( r1_xboole_0 @ A @ B ) =>
% 1.50/1.70       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.50/1.70         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.50/1.70  thf('81', plain,
% 1.50/1.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.50/1.70         (~ (r1_xboole_0 @ X22 @ X23)
% 1.50/1.70          | ((k3_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 1.50/1.70              = (k3_xboole_0 @ X22 @ X24)))),
% 1.50/1.70      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.50/1.70  thf('82', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 1.50/1.70           = (k3_xboole_0 @ sk_B @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['80', '81'])).
% 1.50/1.70  thf('83', plain,
% 1.50/1.70      (![X11 : $i, X12 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X11 @ X12)
% 1.50/1.70          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 1.50/1.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.50/1.70  thf('84', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('85', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.50/1.70           = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('demod', [status(thm)], ['27', '28'])).
% 1.50/1.70  thf('86', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('87', plain,
% 1.50/1.70      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 1.50/1.70          | ~ (r1_xboole_0 @ X11 @ X14))),
% 1.50/1.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.50/1.70  thf('88', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.70          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('sup-', [status(thm)], ['86', '87'])).
% 1.50/1.70  thf('89', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.70          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.50/1.70      inference('sup-', [status(thm)], ['85', '88'])).
% 1.50/1.70  thf('90', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.70          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['84', '89'])).
% 1.50/1.70  thf('91', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((r1_xboole_0 @ X1 @ X0)
% 1.50/1.70          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['83', '90'])).
% 1.50/1.70  thf('92', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 1.50/1.70          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.50/1.70      inference('sup-', [status(thm)], ['82', '91'])).
% 1.50/1.70  thf('93', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.50/1.70      inference('sup-', [status(thm)], ['19', '92'])).
% 1.50/1.70  thf('94', plain, ($false), inference('demod', [status(thm)], ['0', '93'])).
% 1.50/1.70  
% 1.50/1.70  % SZS output end Refutation
% 1.50/1.70  
% 1.50/1.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
