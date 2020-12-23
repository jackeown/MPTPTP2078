%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.20AaaMpKge

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:40 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 113 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :  601 ( 940 expanded)
%              Number of equality atoms :   71 ( 100 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t126_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ) )).

thf('5',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X55 @ X57 ) @ ( k2_zfmisc_1 @ X56 @ X58 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X55 @ X56 ) @ X57 ) @ ( k2_zfmisc_1 @ X55 @ ( k4_xboole_0 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k3_xboole_0 @ X19 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['16','20'])).

thf('22',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','21'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X53 @ X52 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('32',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X55 @ X57 ) @ ( k2_zfmisc_1 @ X56 @ X58 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X55 @ X56 ) @ X57 ) @ ( k2_zfmisc_1 @ X55 @ ( k4_xboole_0 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) @ k1_xboole_0 )
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X19: $i] :
      ( ( k3_xboole_0 @ X19 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('37',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X52 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X53 @ X52 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['29'])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k2_zfmisc_1 @ X53 @ X54 )
        = k1_xboole_0 )
      | ( X54 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('49',plain,(
    ! [X53: $i] :
      ( ( k2_zfmisc_1 @ X53 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['47','49'])).

thf('51',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['29'])).

thf('53',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['30','53'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['28','54'])).

thf('56',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k2_zfmisc_1 @ X53 @ X54 )
        = k1_xboole_0 )
      | ( X53 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('57',plain,(
    ! [X54: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X54 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','55','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.20AaaMpKge
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:29:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 1149 iterations in 0.502s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.98  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i > $i).
% 0.75/0.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.75/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.98  thf(sk_D_type, type, sk_D: $i).
% 0.75/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.98  thf(t138_zfmisc_1, conjecture,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.98     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.75/0.98       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.98         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.98        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.75/0.98          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.98            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.75/0.98  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(t7_xboole_0, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.75/0.98          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.75/0.98  thf('1', plain,
% 0.75/0.98      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.75/0.98      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.75/0.98        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(l32_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      (![X8 : $i, X10 : $i]:
% 0.75/0.98         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.75/0.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.98  thf('4', plain,
% 0.75/0.98      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.75/0.98         (k2_zfmisc_1 @ sk_C_1 @ sk_D)) = (k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.98  thf(t126_zfmisc_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.98     ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =
% 0.75/0.98       ( k2_xboole_0 @
% 0.75/0.98         ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ 
% 0.75/0.98         ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ))).
% 0.75/0.98  thf('5', plain,
% 0.75/0.98      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ (k2_zfmisc_1 @ X55 @ X57) @ (k2_zfmisc_1 @ X56 @ X58))
% 0.75/0.98           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X55 @ X56) @ X57) @ 
% 0.75/0.98              (k2_zfmisc_1 @ X55 @ (k4_xboole_0 @ X57 @ X58))))),
% 0.75/0.98      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 0.75/0.98  thf(commutativity_k2_tarski, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      (![X21 : $i, X22 : $i]:
% 0.75/0.98         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.75/0.98  thf(l51_zfmisc_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.98  thf('7', plain,
% 0.75/0.98      (![X50 : $i, X51 : $i]:
% 0.75/0.98         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.75/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['6', '7'])).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      (![X50 : $i, X51 : $i]:
% 0.75/0.98         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.75/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.75/0.98  thf('10', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['8', '9'])).
% 0.75/0.98  thf(t21_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.75/0.98  thf('11', plain,
% 0.75/0.98      (![X13 : $i, X14 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (X13))),
% 0.75/0.98      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.75/0.98  thf(t4_xboole_0, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.98            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.98       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.75/0.98            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.75/0.98  thf('12', plain,
% 0.75/0.98      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.75/0.98          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.75/0.98      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X2 @ X0)
% 0.75/0.98          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['11', '12'])).
% 0.75/0.98  thf('14', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         (~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.75/0.98          | ~ (r2_hidden @ X2 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['10', '13'])).
% 0.75/0.98  thf('15', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.98         (~ (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ (k4_xboole_0 @ X2 @ X0)) @ 
% 0.75/0.98             (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.75/0.98          | ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X3 @ (k4_xboole_0 @ X2 @ X0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['5', '14'])).
% 0.75/0.98  thf('16', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r1_xboole_0 @ 
% 0.75/0.98             (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_D)) @ k1_xboole_0)
% 0.75/0.98          | ~ (r2_hidden @ X0 @ 
% 0.75/0.98               (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_D))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['4', '15'])).
% 0.75/0.98  thf(t2_boole, axiom,
% 0.75/0.98    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      (![X19 : $i]: ((k3_xboole_0 @ X19 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [t2_boole])).
% 0.75/0.98  thf(d7_xboole_0, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.75/0.98       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      (![X0 : $i, X2 : $i]:
% 0.75/0.98         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['17', '18'])).
% 0.75/0.98  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.75/0.98      inference('simplify', [status(thm)], ['19'])).
% 0.75/0.98  thf('21', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ~ (r2_hidden @ X0 @ 
% 0.75/0.98            (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_D)))),
% 0.75/0.98      inference('demod', [status(thm)], ['16', '20'])).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_D)) = (k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['1', '21'])).
% 0.75/0.98  thf(t113_zfmisc_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.75/0.98       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.75/0.98  thf('23', plain,
% 0.75/0.98      (![X52 : $i, X53 : $i]:
% 0.75/0.98         (((X52) = (k1_xboole_0))
% 0.75/0.98          | ((X53) = (k1_xboole_0))
% 0.75/0.98          | ((k2_zfmisc_1 @ X53 @ X52) != (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.98  thf('24', plain,
% 0.75/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.98        | ((sk_A) = (k1_xboole_0))
% 0.75/0.98        | ((k4_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.98  thf('25', plain,
% 0.75/0.98      ((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 0.75/0.98        | ((sk_A) = (k1_xboole_0)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['24'])).
% 0.75/0.98  thf('26', plain,
% 0.75/0.98      (![X8 : $i, X9 : $i]:
% 0.75/0.98         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.98        | ((sk_A) = (k1_xboole_0))
% 0.75/0.98        | (r1_tarski @ sk_B_1 @ sk_D))),
% 0.75/0.98      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.98  thf('28', plain, (((r1_tarski @ sk_B_1 @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['27'])).
% 0.75/0.98  thf('29', plain,
% 0.75/0.98      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B_1 @ sk_D))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      ((~ (r1_tarski @ sk_B_1 @ sk_D)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 0.75/0.98      inference('split', [status(esa)], ['29'])).
% 0.75/0.98  thf('31', plain,
% 0.75/0.98      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.75/0.98         (k2_zfmisc_1 @ sk_C_1 @ sk_D)) = (k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.98  thf('32', plain,
% 0.75/0.98      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ (k2_zfmisc_1 @ X55 @ X57) @ (k2_zfmisc_1 @ X56 @ X58))
% 0.75/0.98           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X55 @ X56) @ X57) @ 
% 0.75/0.98              (k2_zfmisc_1 @ X55 @ (k4_xboole_0 @ X57 @ X58))))),
% 0.75/0.98      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 0.75/0.98  thf('33', plain,
% 0.75/0.98      (![X13 : $i, X14 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (X13))),
% 0.75/0.98      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2) @ 
% 0.75/0.98           (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.75/0.98           = (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2))),
% 0.75/0.98      inference('sup+', [status(thm)], ['32', '33'])).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      (((k3_xboole_0 @ 
% 0.75/0.98         (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1) @ k1_xboole_0)
% 0.75/0.98         = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['31', '34'])).
% 0.75/0.98  thf('36', plain,
% 0.75/0.98      (![X19 : $i]: ((k3_xboole_0 @ X19 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [t2_boole])).
% 0.75/0.98  thf('37', plain,
% 0.75/0.98      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.98  thf('38', plain,
% 0.75/0.98      (![X52 : $i, X53 : $i]:
% 0.75/0.98         (((X52) = (k1_xboole_0))
% 0.75/0.98          | ((X53) = (k1_xboole_0))
% 0.75/0.98          | ((k2_zfmisc_1 @ X53 @ X52) != (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.98        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['37', '38'])).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      ((((sk_B_1) = (k1_xboole_0))
% 0.75/0.98        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['39'])).
% 0.75/0.98  thf('41', plain,
% 0.75/0.98      (![X8 : $i, X9 : $i]:
% 0.75/0.98         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.98  thf('42', plain,
% 0.75/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0))
% 0.75/0.98        | (r1_tarski @ sk_A @ sk_C_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['40', '41'])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (((r1_tarski @ sk_A @ sk_C_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['42'])).
% 0.75/0.98  thf('44', plain,
% 0.75/0.98      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.75/0.98      inference('split', [status(esa)], ['29'])).
% 0.75/0.98  thf('45', plain,
% 0.75/0.98      ((((sk_B_1) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['43', '44'])).
% 0.75/0.98  thf('46', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('47', plain,
% 0.75/0.98      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.75/0.98         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.98  thf('48', plain,
% 0.75/0.98      (![X53 : $i, X54 : $i]:
% 0.75/0.98         (((k2_zfmisc_1 @ X53 @ X54) = (k1_xboole_0))
% 0.75/0.98          | ((X54) != (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.98  thf('49', plain,
% 0.75/0.98      (![X53 : $i]: ((k2_zfmisc_1 @ X53 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.98      inference('simplify', [status(thm)], ['48'])).
% 0.75/0.98  thf('50', plain,
% 0.75/0.98      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['47', '49'])).
% 0.75/0.98  thf('51', plain, (((r1_tarski @ sk_A @ sk_C_1))),
% 0.75/0.98      inference('simplify', [status(thm)], ['50'])).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      (~ ((r1_tarski @ sk_B_1 @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C_1))),
% 0.75/0.98      inference('split', [status(esa)], ['29'])).
% 0.75/0.98  thf('53', plain, (~ ((r1_tarski @ sk_B_1 @ sk_D))),
% 0.75/0.98      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.75/0.98  thf('54', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.75/0.98      inference('simpl_trail', [status(thm)], ['30', '53'])).
% 0.75/0.98  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.98      inference('clc', [status(thm)], ['28', '54'])).
% 0.75/0.98  thf('56', plain,
% 0.75/0.98      (![X53 : $i, X54 : $i]:
% 0.75/0.98         (((k2_zfmisc_1 @ X53 @ X54) = (k1_xboole_0))
% 0.75/0.98          | ((X53) != (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.75/0.98  thf('57', plain,
% 0.75/0.98      (![X54 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X54) = (k1_xboole_0))),
% 0.75/0.98      inference('simplify', [status(thm)], ['56'])).
% 0.75/0.98  thf('58', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.75/0.98      inference('demod', [status(thm)], ['0', '55', '57'])).
% 0.75/0.98  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.82/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
