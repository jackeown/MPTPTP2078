%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0021+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VoJWGdqLF5

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:41 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   61 (  82 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  420 ( 643 expanded)
%              Number of equality atoms :   37 (  55 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X115: $i,X116: $i] :
      ( r1_tarski @ ( X115 @ ( k2_xboole_0 @ ( X115 @ X116 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ! [X115: $i,X116: $i] :
      ( r1_tarski @ ( X115 @ ( k2_xboole_0 @ ( X115 @ X116 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t14_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( C @ B ) )
        & ! [D: $i] :
            ( ( ( r1_tarski @ ( A @ D ) )
              & ( r1_tarski @ ( C @ D ) ) )
           => ( r1_tarski @ ( B @ D ) ) ) )
     => ( B
        = ( k2_xboole_0 @ ( A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( r1_tarski @ ( C @ B ) )
          & ! [D: $i] :
              ( ( ( r1_tarski @ ( A @ D ) )
                & ( r1_tarski @ ( C @ D ) ) )
             => ( r1_tarski @ ( B @ D ) ) ) )
       => ( B
          = ( k2_xboole_0 @ ( A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_xboole_1])).

thf('3',plain,(
    ! [X97: $i] :
      ( ( r1_tarski @ ( sk_B_2 @ X97 ) )
      | ~ ( r1_tarski @ ( sk_C_5 @ X97 ) )
      | ~ ( r1_tarski @ ( sk_A_2 @ X97 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_5 @ X0 ) ) ) )
      | ( r1_tarski @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_C_5 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( X0 @ sk_C_5 ) ) ) )
      | ( r1_tarski @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_C_5 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_tarski @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('9',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) )
    = ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('11',plain,(
    ! [X111: $i,X112: $i] :
      ( ( k2_xboole_0 @ ( X111 @ ( k2_xboole_0 @ ( X111 @ X112 ) ) ) )
      = ( k2_xboole_0 @ ( X111 @ X112 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('12',plain,(
    ! [X115: $i,X116: $i] :
      ( r1_tarski @ ( X115 @ ( k2_xboole_0 @ ( X115 @ X116 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('13',plain,(
    r1_tarski @ ( sk_C_5 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) )
    = sk_B_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('19',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X88 @ X90 ) @ X89 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( X1 @ X0 ) @ X2 ) )
      | ( r1_tarski @ ( X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_B_2 @ X0 ) )
      | ( r1_tarski @ ( sk_C_5 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) @ sk_C_5 ) )
      = ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) @ sk_C_5 ) )
      = ( k2_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X115: $i,X116: $i] :
      ( r1_tarski @ ( X115 @ ( k2_xboole_0 @ ( X115 @ X116 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) @ sk_C_5 ) )
      = ( k2_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('36',plain,(
    ! [X104: $i,X105: $i,X106: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X104 @ X105 ) @ X106 ) )
      = ( k2_xboole_0 @ ( X104 @ ( k2_xboole_0 @ ( X105 @ X106 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( X0 @ sk_C_5 ) ) ) )
      = ( k2_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(demod,[status(thm)],['10','37','38'])).

thf('40',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = sk_B_2 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_B_2
    = ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    sk_B_2
 != ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
