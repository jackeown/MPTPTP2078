%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.upPo19vTKq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:13 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 105 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  661 ( 917 expanded)
%              Number of equality atoms :   38 (  55 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t124_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
        = ( k2_zfmisc_1 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
          = ( k2_zfmisc_1 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
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

thf('2',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['25','36'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X19 @ X21 ) @ ( k3_xboole_0 @ X20 @ X22 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('42',plain,(
    r1_tarski @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_C_1 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ sk_C_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_C_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ sk_C_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['51'])).

thf('53',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C_1 )
 != ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','39','40','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.upPo19vTKq
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.86  % Solved by: fo/fo7.sh
% 0.71/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.86  % done 993 iterations in 0.415s
% 0.71/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.86  % SZS output start Refutation
% 0.71/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.71/0.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.71/0.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.71/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.86  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.71/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.71/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.86  thf(t124_zfmisc_1, conjecture,
% 0.71/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.86     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.71/0.86       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.71/0.86         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.71/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.86    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.86        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.71/0.86          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.71/0.86            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.71/0.86    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.71/0.86  thf('0', plain,
% 0.71/0.86      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D_1) @ 
% 0.71/0.86         (k2_zfmisc_1 @ sk_B @ sk_C_1)) != (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.71/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.86  thf(commutativity_k3_xboole_0, axiom,
% 0.71/0.86    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.71/0.86  thf('1', plain,
% 0.71/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.86  thf('2', plain,
% 0.71/0.86      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1) @ 
% 0.71/0.86         (k2_zfmisc_1 @ sk_A @ sk_D_1)) != (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.71/0.86      inference('demod', [status(thm)], ['0', '1'])).
% 0.71/0.86  thf(d3_tarski, axiom,
% 0.71/0.86    (![A:$i,B:$i]:
% 0.71/0.86     ( ( r1_tarski @ A @ B ) <=>
% 0.71/0.86       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.71/0.86  thf('3', plain,
% 0.71/0.86      (![X3 : $i, X5 : $i]:
% 0.71/0.86         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.71/0.86      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.86  thf(t48_xboole_1, axiom,
% 0.71/0.86    (![A:$i,B:$i]:
% 0.71/0.86     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.71/0.86  thf('4', plain,
% 0.71/0.86      (![X17 : $i, X18 : $i]:
% 0.71/0.86         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.71/0.86           = (k3_xboole_0 @ X17 @ X18))),
% 0.71/0.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.86  thf('5', plain,
% 0.71/0.86      (![X3 : $i, X5 : $i]:
% 0.71/0.86         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.71/0.86      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.86  thf('6', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.71/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.86  thf('7', plain,
% 0.71/0.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.71/0.86         (~ (r2_hidden @ X2 @ X3)
% 0.71/0.86          | (r2_hidden @ X2 @ X4)
% 0.71/0.86          | ~ (r1_tarski @ X3 @ X4))),
% 0.71/0.86      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.86  thf('8', plain,
% 0.71/0.86      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.71/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.71/0.86  thf('9', plain,
% 0.71/0.86      (![X0 : $i]:
% 0.71/0.86         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.71/0.86      inference('sup-', [status(thm)], ['5', '8'])).
% 0.71/0.86  thf(d5_xboole_0, axiom,
% 0.71/0.86    (![A:$i,B:$i,C:$i]:
% 0.71/0.86     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.71/0.86       ( ![D:$i]:
% 0.71/0.86         ( ( r2_hidden @ D @ C ) <=>
% 0.71/0.86           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.71/0.86  thf('10', plain,
% 0.71/0.86      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.71/0.86         (~ (r2_hidden @ X6 @ X7)
% 0.71/0.86          | (r2_hidden @ X6 @ X8)
% 0.71/0.86          | (r2_hidden @ X6 @ X9)
% 0.71/0.86          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.71/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.86  thf('11', plain,
% 0.71/0.86      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.71/0.86         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.71/0.86          | (r2_hidden @ X6 @ X8)
% 0.71/0.86          | ~ (r2_hidden @ X6 @ X7))),
% 0.71/0.86      inference('simplify', [status(thm)], ['10'])).
% 0.71/0.87  thf('12', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]:
% 0.71/0.87         ((r1_tarski @ sk_A @ X0)
% 0.71/0.87          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1)
% 0.71/0.87          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X1)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['9', '11'])).
% 0.71/0.87  thf('13', plain,
% 0.71/0.87      (![X3 : $i, X5 : $i]:
% 0.71/0.87         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.87  thf('14', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ X0)
% 0.71/0.87          | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.71/0.87          | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['12', '13'])).
% 0.71/0.87  thf('15', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.71/0.87          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ X0))),
% 0.71/0.87      inference('simplify', [status(thm)], ['14'])).
% 0.71/0.87  thf('16', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((r2_hidden @ (sk_C @ (k3_xboole_0 @ sk_B @ X0) @ sk_A) @ 
% 0.71/0.87           (k4_xboole_0 @ sk_B @ X0))
% 0.71/0.87          | (r1_tarski @ sk_A @ 
% 0.71/0.87             (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0))))),
% 0.71/0.87      inference('sup+', [status(thm)], ['4', '15'])).
% 0.71/0.87  thf('17', plain,
% 0.71/0.87      (![X17 : $i, X18 : $i]:
% 0.71/0.87         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.71/0.87           = (k3_xboole_0 @ X17 @ X18))),
% 0.71/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.87  thf('18', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((r2_hidden @ (sk_C @ (k3_xboole_0 @ sk_B @ X0) @ sk_A) @ 
% 0.71/0.87           (k4_xboole_0 @ sk_B @ X0))
% 0.71/0.87          | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.71/0.87      inference('demod', [status(thm)], ['16', '17'])).
% 0.71/0.87  thf('19', plain,
% 0.71/0.87      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.71/0.87         (~ (r2_hidden @ X10 @ X9)
% 0.71/0.87          | ~ (r2_hidden @ X10 @ X8)
% 0.71/0.87          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.71/0.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.87  thf('20', plain,
% 0.71/0.87      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.71/0.87         (~ (r2_hidden @ X10 @ X8)
% 0.71/0.87          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.71/0.87      inference('simplify', [status(thm)], ['19'])).
% 0.71/0.87  thf('21', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.71/0.87          | ~ (r2_hidden @ (sk_C @ (k3_xboole_0 @ sk_B @ X0) @ sk_A) @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['18', '20'])).
% 0.71/0.87  thf('22', plain,
% 0.71/0.87      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.71/0.87        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['3', '21'])).
% 0.71/0.87  thf('23', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.71/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.71/0.87  thf(d10_xboole_0, axiom,
% 0.71/0.87    (![A:$i,B:$i]:
% 0.71/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.71/0.87  thf('24', plain,
% 0.71/0.87      (![X12 : $i, X14 : $i]:
% 0.71/0.87         (((X12) = (X14))
% 0.71/0.87          | ~ (r1_tarski @ X14 @ X12)
% 0.71/0.87          | ~ (r1_tarski @ X12 @ X14))),
% 0.71/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.71/0.87  thf('25', plain,
% 0.71/0.87      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)
% 0.71/0.87        | ((k3_xboole_0 @ sk_B @ sk_A) = (sk_A)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['23', '24'])).
% 0.71/0.87  thf('26', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.87  thf('27', plain,
% 0.71/0.87      (![X17 : $i, X18 : $i]:
% 0.71/0.87         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.71/0.87           = (k3_xboole_0 @ X17 @ X18))),
% 0.71/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.87  thf('28', plain,
% 0.71/0.87      (![X3 : $i, X5 : $i]:
% 0.71/0.87         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.87  thf('29', plain,
% 0.71/0.87      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.71/0.87         (~ (r2_hidden @ X10 @ X9)
% 0.71/0.87          | (r2_hidden @ X10 @ X7)
% 0.71/0.87          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.71/0.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.87  thf('30', plain,
% 0.71/0.87      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.71/0.87         ((r2_hidden @ X10 @ X7)
% 0.71/0.87          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.71/0.87      inference('simplify', [status(thm)], ['29'])).
% 0.71/0.87  thf('31', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.87         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.71/0.87          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['28', '30'])).
% 0.71/0.87  thf('32', plain,
% 0.71/0.87      (![X3 : $i, X5 : $i]:
% 0.71/0.87         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.87  thf('33', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]:
% 0.71/0.87         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.71/0.87          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['31', '32'])).
% 0.71/0.87  thf('34', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.71/0.87      inference('simplify', [status(thm)], ['33'])).
% 0.71/0.87  thf('35', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.71/0.87      inference('sup+', [status(thm)], ['27', '34'])).
% 0.71/0.87  thf('36', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.71/0.87      inference('sup+', [status(thm)], ['26', '35'])).
% 0.71/0.87  thf('37', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['25', '36'])).
% 0.71/0.87  thf(t123_zfmisc_1, axiom,
% 0.71/0.87    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.87     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.71/0.87       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.71/0.87  thf('38', plain,
% 0.71/0.87      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.71/0.87         ((k2_zfmisc_1 @ (k3_xboole_0 @ X19 @ X21) @ (k3_xboole_0 @ X20 @ X22))
% 0.71/0.87           = (k3_xboole_0 @ (k2_zfmisc_1 @ X19 @ X20) @ 
% 0.71/0.87              (k2_zfmisc_1 @ X21 @ X22)))),
% 0.71/0.87      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.71/0.87  thf('39', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]:
% 0.71/0.87         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0))
% 0.71/0.87           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ X1) @ 
% 0.71/0.87              (k2_zfmisc_1 @ sk_A @ X0)))),
% 0.71/0.87      inference('sup+', [status(thm)], ['37', '38'])).
% 0.71/0.87  thf('40', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.87  thf('41', plain,
% 0.71/0.87      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.71/0.87         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.71/0.87          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 0.71/0.87          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.71/0.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.87  thf('42', plain, ((r1_tarski @ sk_C_1 @ sk_D_1)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('43', plain,
% 0.71/0.87      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.71/0.87         (~ (r2_hidden @ X2 @ X3)
% 0.71/0.87          | (r2_hidden @ X2 @ X4)
% 0.71/0.87          | ~ (r1_tarski @ X3 @ X4))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.87  thf('44', plain,
% 0.71/0.87      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['42', '43'])).
% 0.71/0.87  thf('45', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]:
% 0.71/0.87         ((r2_hidden @ (sk_D @ X1 @ X0 @ sk_C_1) @ X1)
% 0.71/0.87          | ((X1) = (k4_xboole_0 @ sk_C_1 @ X0))
% 0.71/0.87          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_C_1) @ sk_D_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['41', '44'])).
% 0.71/0.87  thf('46', plain,
% 0.71/0.87      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.71/0.87         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.71/0.87          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 0.71/0.87          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.71/0.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.87  thf('47', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (((X0) = (k4_xboole_0 @ sk_C_1 @ sk_D_1))
% 0.71/0.87          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C_1) @ X0)
% 0.71/0.87          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C_1) @ X0)
% 0.71/0.87          | ((X0) = (k4_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['45', '46'])).
% 0.71/0.87  thf('48', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C_1) @ X0)
% 0.71/0.87          | ((X0) = (k4_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 0.71/0.87      inference('simplify', [status(thm)], ['47'])).
% 0.71/0.87  thf(t3_boole, axiom,
% 0.71/0.87    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.71/0.87  thf('49', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.71/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.87  thf('50', plain,
% 0.71/0.87      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.71/0.87         (~ (r2_hidden @ X10 @ X8)
% 0.71/0.87          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.71/0.87      inference('simplify', [status(thm)], ['19'])).
% 0.71/0.87  thf('51', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]:
% 0.71/0.87         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['49', '50'])).
% 0.71/0.87  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.71/0.87      inference('condensation', [status(thm)], ['51'])).
% 0.71/0.87  thf('53', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['48', '52'])).
% 0.71/0.87  thf('54', plain,
% 0.71/0.87      (![X17 : $i, X18 : $i]:
% 0.71/0.87         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.71/0.87           = (k3_xboole_0 @ X17 @ X18))),
% 0.71/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.87  thf('55', plain,
% 0.71/0.87      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.71/0.87      inference('sup+', [status(thm)], ['53', '54'])).
% 0.71/0.87  thf('56', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.71/0.87      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.87  thf('57', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.87  thf('58', plain, (((sk_C_1) = (k3_xboole_0 @ sk_D_1 @ sk_C_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.71/0.87  thf('59', plain,
% 0.71/0.87      (((k2_zfmisc_1 @ sk_A @ sk_C_1) != (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.71/0.87      inference('demod', [status(thm)], ['2', '39', '40', '58'])).
% 0.71/0.87  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.71/0.87  
% 0.71/0.87  % SZS output end Refutation
% 0.71/0.87  
% 0.74/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
