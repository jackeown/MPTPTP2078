%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AfwObNV6uh

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:23 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 121 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  637 (1028 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_3 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_3 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference(simplify,[status(thm)],['7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

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
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    r1_xboole_0 @ sk_C_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['20','32'])).

thf('34',plain,(
    r2_hidden @ sk_D @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( X30 = X27 )
      | ( X29
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('47',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('48',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['55'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('57',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_xboole_0 @ X23 @ X24 )
      | ~ ( r1_xboole_0 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['8','58'])).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_3 ) @ sk_B ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AfwObNV6uh
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:17:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.97/1.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.97/1.18  % Solved by: fo/fo7.sh
% 0.97/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.18  % done 1753 iterations in 0.741s
% 0.97/1.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.97/1.18  % SZS output start Refutation
% 0.97/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.18  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.97/1.18  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.97/1.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.97/1.18  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.18  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.97/1.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.97/1.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.97/1.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.97/1.18  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.97/1.18  thf(sk_D_type, type, sk_D: $i).
% 0.97/1.18  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.97/1.18  thf(t149_zfmisc_1, conjecture,
% 0.97/1.18    (![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.18     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.97/1.18         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.97/1.18       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.97/1.18  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.18    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.18        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.97/1.18            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.97/1.18          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.97/1.18    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.97/1.18  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_3) @ sk_B)),
% 0.97/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.18  thf('1', plain, ((r1_xboole_0 @ sk_C_3 @ sk_B)),
% 0.97/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.18  thf(d7_xboole_0, axiom,
% 0.97/1.18    (![A:$i,B:$i]:
% 0.97/1.18     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.97/1.18       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.97/1.18  thf('2', plain,
% 0.97/1.18      (![X6 : $i, X7 : $i]:
% 0.97/1.18         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.97/1.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.97/1.18  thf('3', plain, (((k3_xboole_0 @ sk_C_3 @ sk_B) = (k1_xboole_0))),
% 0.97/1.18      inference('sup-', [status(thm)], ['1', '2'])).
% 0.97/1.18  thf(commutativity_k3_xboole_0, axiom,
% 0.97/1.18    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.97/1.18  thf('4', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.97/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.97/1.18  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_3) = (k1_xboole_0))),
% 0.97/1.18      inference('demod', [status(thm)], ['3', '4'])).
% 0.97/1.18  thf('6', plain,
% 0.97/1.18      (![X6 : $i, X8 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.97/1.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.97/1.18  thf('7', plain,
% 0.97/1.18      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.97/1.18      inference('sup-', [status(thm)], ['5', '6'])).
% 0.97/1.18  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_3)),
% 0.97/1.18      inference('simplify', [status(thm)], ['7'])).
% 0.97/1.18  thf(d3_tarski, axiom,
% 0.97/1.18    (![A:$i,B:$i]:
% 0.97/1.18     ( ( r1_tarski @ A @ B ) <=>
% 0.97/1.18       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.97/1.18  thf('9', plain,
% 0.97/1.18      (![X3 : $i, X5 : $i]:
% 0.97/1.18         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.97/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.18  thf('10', plain,
% 0.97/1.18      (![X3 : $i, X5 : $i]:
% 0.97/1.18         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.97/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.18  thf('11', plain,
% 0.97/1.18      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.97/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.18  thf('12', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.97/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.97/1.18  thf('13', plain,
% 0.97/1.18      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.97/1.18      inference('demod', [status(thm)], ['11', '12'])).
% 0.97/1.18  thf('14', plain,
% 0.97/1.18      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.97/1.18         (~ (r2_hidden @ X2 @ X3)
% 0.97/1.18          | (r2_hidden @ X2 @ X4)
% 0.97/1.18          | ~ (r1_tarski @ X3 @ X4))),
% 0.97/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.18  thf('15', plain,
% 0.97/1.18      (![X0 : $i]:
% 0.97/1.18         ((r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 0.97/1.18          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.97/1.18      inference('sup-', [status(thm)], ['13', '14'])).
% 0.97/1.18  thf('16', plain,
% 0.97/1.18      (![X0 : $i]:
% 0.97/1.18         ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.97/1.18          | (r2_hidden @ (sk_C @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)) @ 
% 0.97/1.18             (k1_tarski @ sk_D)))),
% 0.97/1.18      inference('sup-', [status(thm)], ['10', '15'])).
% 0.97/1.18  thf(t3_xboole_0, axiom,
% 0.97/1.18    (![A:$i,B:$i]:
% 0.97/1.18     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.97/1.18            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.97/1.18       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.97/1.18            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.97/1.18  thf('17', plain,
% 0.97/1.18      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.97/1.18         (~ (r2_hidden @ X11 @ X9)
% 0.97/1.18          | ~ (r2_hidden @ X11 @ X12)
% 0.97/1.18          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.97/1.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.97/1.18  thf('18', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i]:
% 0.97/1.18         ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.97/1.18          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ X1)
% 0.97/1.18          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)) @ X1))),
% 0.97/1.18      inference('sup-', [status(thm)], ['16', '17'])).
% 0.97/1.18  thf('19', plain,
% 0.97/1.18      (![X0 : $i]:
% 0.97/1.18         ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.97/1.18          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.97/1.18          | (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ X0))),
% 0.97/1.18      inference('sup-', [status(thm)], ['9', '18'])).
% 0.97/1.18  thf(t48_xboole_1, axiom,
% 0.97/1.18    (![A:$i,B:$i]:
% 0.97/1.18     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.97/1.18  thf('20', plain,
% 0.97/1.18      (![X20 : $i, X21 : $i]:
% 0.97/1.18         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.97/1.18           = (k3_xboole_0 @ X20 @ X21))),
% 0.97/1.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.97/1.18  thf('21', plain, ((r1_xboole_0 @ sk_C_3 @ sk_B)),
% 0.97/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.18  thf('22', plain,
% 0.97/1.18      (![X9 : $i, X10 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.97/1.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.97/1.18  thf(t36_xboole_1, axiom,
% 0.97/1.18    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.97/1.18  thf('23', plain,
% 0.97/1.18      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.97/1.18      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.97/1.18  thf('24', plain,
% 0.97/1.18      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.97/1.18         (~ (r2_hidden @ X2 @ X3)
% 0.97/1.18          | (r2_hidden @ X2 @ X4)
% 0.97/1.18          | ~ (r1_tarski @ X3 @ X4))),
% 0.97/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.18  thf('25', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.18         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.97/1.18      inference('sup-', [status(thm)], ['23', '24'])).
% 0.97/1.18  thf('26', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.97/1.18          | (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.97/1.18      inference('sup-', [status(thm)], ['22', '25'])).
% 0.97/1.18  thf('27', plain,
% 0.97/1.18      (![X9 : $i, X10 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X10))),
% 0.97/1.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.97/1.18  thf('28', plain,
% 0.97/1.18      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.97/1.18         (~ (r2_hidden @ X11 @ X9)
% 0.97/1.18          | ~ (r2_hidden @ X11 @ X12)
% 0.97/1.18          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.97/1.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.97/1.18  thf('29', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X1 @ X0)
% 0.97/1.18          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.97/1.18          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.97/1.18      inference('sup-', [status(thm)], ['27', '28'])).
% 0.97/1.18  thf('30', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.97/1.18          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.97/1.18          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 0.97/1.18      inference('sup-', [status(thm)], ['26', '29'])).
% 0.97/1.18  thf('31', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.18         (~ (r1_xboole_0 @ X2 @ X0)
% 0.97/1.18          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 0.97/1.18      inference('simplify', [status(thm)], ['30'])).
% 0.97/1.18  thf('32', plain,
% 0.97/1.18      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C_3)),
% 0.97/1.18      inference('sup-', [status(thm)], ['21', '31'])).
% 0.97/1.18  thf('33', plain,
% 0.97/1.18      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_3)),
% 0.97/1.18      inference('sup+', [status(thm)], ['20', '32'])).
% 0.97/1.18  thf('34', plain, ((r2_hidden @ sk_D @ sk_C_3)),
% 0.97/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.18  thf('35', plain,
% 0.97/1.18      (![X9 : $i, X10 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.97/1.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.97/1.18  thf(d1_tarski, axiom,
% 0.97/1.18    (![A:$i,B:$i]:
% 0.97/1.18     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.97/1.18       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.97/1.18  thf('36', plain,
% 0.97/1.18      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.97/1.18         (~ (r2_hidden @ X30 @ X29)
% 0.97/1.18          | ((X30) = (X27))
% 0.97/1.18          | ((X29) != (k1_tarski @ X27)))),
% 0.97/1.18      inference('cnf', [status(esa)], [d1_tarski])).
% 0.97/1.18  thf('37', plain,
% 0.97/1.18      (![X27 : $i, X30 : $i]:
% 0.97/1.18         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 0.97/1.18      inference('simplify', [status(thm)], ['36'])).
% 0.97/1.18  thf('38', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.97/1.18          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.97/1.18      inference('sup-', [status(thm)], ['35', '37'])).
% 0.97/1.18  thf('39', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X1 @ X0)
% 0.97/1.18          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.97/1.18          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.97/1.18      inference('sup-', [status(thm)], ['27', '28'])).
% 0.97/1.18  thf('40', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.18         (~ (r2_hidden @ X0 @ X1)
% 0.97/1.18          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 0.97/1.18          | ~ (r1_xboole_0 @ X2 @ X1)
% 0.97/1.18          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2))),
% 0.97/1.18      inference('sup-', [status(thm)], ['38', '39'])).
% 0.97/1.18  thf('41', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.18         (~ (r1_xboole_0 @ X2 @ X1)
% 0.97/1.18          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 0.97/1.18          | ~ (r2_hidden @ X0 @ X1))),
% 0.97/1.18      inference('simplify', [status(thm)], ['40'])).
% 0.97/1.18  thf('42', plain,
% 0.97/1.18      (![X0 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.97/1.18          | ~ (r1_xboole_0 @ X0 @ sk_C_3))),
% 0.97/1.18      inference('sup-', [status(thm)], ['34', '41'])).
% 0.97/1.18  thf('43', plain,
% 0.97/1.18      (![X0 : $i]:
% 0.97/1.18         (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.97/1.18      inference('sup-', [status(thm)], ['33', '42'])).
% 0.97/1.18  thf('44', plain,
% 0.97/1.18      (![X0 : $i]:
% 0.97/1.18         ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.97/1.18          | (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ X0))),
% 0.97/1.18      inference('demod', [status(thm)], ['19', '43'])).
% 0.97/1.18  thf('45', plain,
% 0.97/1.18      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)),
% 0.97/1.18      inference('simplify', [status(thm)], ['44'])).
% 0.97/1.18  thf('46', plain,
% 0.97/1.18      (![X3 : $i, X5 : $i]:
% 0.97/1.18         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.97/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.18  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.97/1.18  thf('47', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.97/1.18      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.97/1.18  thf(l24_zfmisc_1, axiom,
% 0.97/1.18    (![A:$i,B:$i]:
% 0.97/1.18     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.97/1.18  thf('48', plain,
% 0.97/1.18      (![X38 : $i, X39 : $i]:
% 0.97/1.18         (~ (r1_xboole_0 @ (k1_tarski @ X38) @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 0.97/1.18      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.97/1.18  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.97/1.18      inference('sup-', [status(thm)], ['47', '48'])).
% 0.97/1.18  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.97/1.18      inference('sup-', [status(thm)], ['46', '49'])).
% 0.97/1.18  thf(d10_xboole_0, axiom,
% 0.97/1.18    (![A:$i,B:$i]:
% 0.97/1.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.97/1.18  thf('51', plain,
% 0.97/1.18      (![X13 : $i, X15 : $i]:
% 0.97/1.18         (((X13) = (X15))
% 0.97/1.18          | ~ (r1_tarski @ X15 @ X13)
% 0.97/1.18          | ~ (r1_tarski @ X13 @ X15))),
% 0.97/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.18  thf('52', plain,
% 0.97/1.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.97/1.18      inference('sup-', [status(thm)], ['50', '51'])).
% 0.97/1.18  thf('53', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.97/1.18      inference('sup-', [status(thm)], ['45', '52'])).
% 0.97/1.18  thf('54', plain,
% 0.97/1.18      (![X6 : $i, X8 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.97/1.18      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.97/1.18  thf('55', plain,
% 0.97/1.18      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.97/1.18      inference('sup-', [status(thm)], ['53', '54'])).
% 0.97/1.18  thf('56', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.97/1.18      inference('simplify', [status(thm)], ['55'])).
% 0.97/1.18  thf(t70_xboole_1, axiom,
% 0.97/1.18    (![A:$i,B:$i,C:$i]:
% 0.97/1.18     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.97/1.18            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.97/1.18       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.97/1.18            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.97/1.18  thf('57', plain,
% 0.97/1.18      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 0.97/1.18          | ~ (r1_xboole_0 @ X23 @ X24)
% 0.97/1.18          | ~ (r1_xboole_0 @ X23 @ X25))),
% 0.97/1.18      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.97/1.18  thf('58', plain,
% 0.97/1.18      (![X0 : $i]:
% 0.97/1.18         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.97/1.18          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.97/1.18      inference('sup-', [status(thm)], ['56', '57'])).
% 0.97/1.18  thf('59', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_3))),
% 0.97/1.18      inference('sup-', [status(thm)], ['8', '58'])).
% 0.97/1.18  thf('60', plain,
% 0.97/1.18      (![X9 : $i, X10 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.97/1.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.97/1.18  thf('61', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X1 @ X0)
% 0.97/1.18          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.97/1.18          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.97/1.18      inference('sup-', [status(thm)], ['27', '28'])).
% 0.97/1.18  thf('62', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i]:
% 0.97/1.18         ((r1_xboole_0 @ X0 @ X1)
% 0.97/1.18          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.97/1.18          | (r1_xboole_0 @ X0 @ X1))),
% 0.97/1.18      inference('sup-', [status(thm)], ['60', '61'])).
% 0.97/1.18  thf('63', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i]:
% 0.97/1.18         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.97/1.18      inference('simplify', [status(thm)], ['62'])).
% 0.97/1.18  thf('64', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_3) @ sk_B)),
% 0.97/1.18      inference('sup-', [status(thm)], ['59', '63'])).
% 0.97/1.18  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 0.97/1.18  
% 0.97/1.18  % SZS output end Refutation
% 0.97/1.18  
% 0.97/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
