%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MogmZCgZdQ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 193 expanded)
%              Number of leaves         :   19 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  593 (1532 expanded)
%              Number of equality atoms :   36 (  98 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t127_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ B )
          | ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_D )
      = sk_C_1 )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
      = ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X15 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_C @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ sk_C_1 @ sk_C_1 ) ) )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('23',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('34',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_C @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) @ k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['10','32','34'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('42',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_C @ ( k2_zfmisc_1 @ sk_B @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_C @ ( k2_zfmisc_1 @ sk_B @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) @ k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('49',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['46','49'])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('54',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['35','54'])).

thf('56',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MogmZCgZdQ
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 177 iterations in 0.063s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(t127_zfmisc_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.22/0.52       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.22/0.52          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.22/0.52          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((r1_xboole_0 @ sk_C_1 @ sk_D)) <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['1'])).
% 0.22/0.52  thf(t83_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((((k4_xboole_0 @ sk_C_1 @ sk_D) = (sk_C_1)))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(t48_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.22/0.52           = (k3_xboole_0 @ X7 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((((k4_xboole_0 @ sk_C_1 @ sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_D)))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf(t123_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.22/0.52       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         ((k2_zfmisc_1 @ (k3_xboole_0 @ X15 @ X17) @ (k3_xboole_0 @ X16 @ X18))
% 0.22/0.52           = (k3_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 0.22/0.52              (k2_zfmisc_1 @ X17 @ X18)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.22/0.52  thf(t4_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X2 @ X3)
% 0.22/0.52          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((r2_hidden @ 
% 0.22/0.52           (sk_C @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.52          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((![X0 : $i, X1 : $i]:
% 0.22/0.52          ((r2_hidden @ 
% 0.22/0.52            (sk_C @ (k2_zfmisc_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ X1 @ sk_C_1)) @ 
% 0.22/0.52            (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.22/0.52             (k4_xboole_0 @ sk_C_1 @ sk_C_1)))
% 0.22/0.52           | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ 
% 0.22/0.52              (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '9'])).
% 0.22/0.52  thf(t2_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.22/0.52           = (k3_xboole_0 @ X7 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X9 : $i, X11 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ X1 @ X0) != (X1))
% 0.22/0.52          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_xboole_0) != (X0))
% 0.22/0.52          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      ((r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      ((r1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X2 @ X3)
% 0.22/0.52          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.52          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.22/0.52          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '24'])).
% 0.22/0.52  thf('26', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.52  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.22/0.52           = (k3_xboole_0 @ X7 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.52  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf(t113_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.22/0.52          | ((X14) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      ((![X0 : $i, X1 : $i]:
% 0.22/0.52          ((r2_hidden @ 
% 0.22/0.52            (sk_C @ (k2_zfmisc_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ X1 @ sk_C_1)) @ 
% 0.22/0.52            k1_xboole_0)
% 0.22/0.52           | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ 
% 0.22/0.52              (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['10', '32', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['1'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.22/0.52           = (k3_xboole_0 @ X7 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((r2_hidden @ 
% 0.22/0.52           (sk_C @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1)) @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.52          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      ((![X0 : $i, X1 : $i]:
% 0.22/0.52          ((r2_hidden @ 
% 0.22/0.52            (sk_C @ (k2_zfmisc_1 @ sk_B @ X0) @ (k2_zfmisc_1 @ sk_A @ X1)) @ 
% 0.22/0.52            (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_A) @ 
% 0.22/0.52             (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.52           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.22/0.52              (k2_zfmisc_1 @ sk_B @ X0))))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.22/0.52          | ((X13) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      ((![X0 : $i, X1 : $i]:
% 0.22/0.52          ((r2_hidden @ 
% 0.22/0.52            (sk_C @ (k2_zfmisc_1 @ sk_B @ X0) @ (k2_zfmisc_1 @ sk_A @ X1)) @ 
% 0.22/0.52            k1_xboole_0)
% 0.22/0.52           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.22/0.52              (k2_zfmisc_1 @ sk_B @ X0))))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '43', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '25'])).
% 0.22/0.52  thf('49', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      ((![X0 : $i, X1 : $i]:
% 0.22/0.52          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.22/0.52         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('clc', [status(thm)], ['46', '49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.22/0.52          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('52', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (((r1_xboole_0 @ sk_C_1 @ sk_D)) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('split', [status(esa)], ['1'])).
% 0.22/0.52  thf('54', plain, (((r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r2_hidden @ 
% 0.22/0.52           (sk_C @ (k2_zfmisc_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ X1 @ sk_C_1)) @ 
% 0.22/0.52           k1_xboole_0)
% 0.22/0.52          | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ 
% 0.22/0.52             (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['35', '54'])).
% 0.22/0.52  thf('56', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ (k2_zfmisc_1 @ X0 @ sk_D))),
% 0.22/0.52      inference('clc', [status(thm)], ['55', '56'])).
% 0.22/0.52  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
