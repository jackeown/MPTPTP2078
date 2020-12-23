%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pOsHtNjGjG

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:51 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 376 expanded)
%              Number of leaves         :   13 ( 113 expanded)
%              Depth                    :   22
%              Number of atoms          :  898 (4463 expanded)
%              Number of equality atoms :   50 ( 259 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t20_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ A @ C )
          & ! [D: $i] :
              ( ( ( r1_tarski @ D @ B )
                & ( r1_tarski @ D @ C ) )
             => ( r1_tarski @ D @ A ) ) )
       => ( A
          = ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_xboole_1])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) @ ( k3_xboole_0 @ X2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_xboole_0 @ sk_A @ sk_A ) ) @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['25','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('58',plain,(
    ! [X14: $i] :
      ( ( r1_tarski @ X14 @ sk_A )
      | ~ ( r1_tarski @ X14 @ sk_C_1 )
      | ~ ( r1_tarski @ X14 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X1 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('67',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('69',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('70',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
      = sk_A )
    | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
      = sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    sk_A
 != ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('75',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['54','75'])).

thf('77',plain,(
    sk_A
 != ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pOsHtNjGjG
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 1.64/1.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.64/1.85  % Solved by: fo/fo7.sh
% 1.64/1.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.85  % done 1982 iterations in 1.391s
% 1.64/1.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.64/1.85  % SZS output start Refutation
% 1.64/1.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.64/1.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.64/1.85  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.85  thf(sk_B_type, type, sk_B: $i).
% 1.64/1.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.64/1.85  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.64/1.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.64/1.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.64/1.85  thf(d4_xboole_0, axiom,
% 1.64/1.85    (![A:$i,B:$i,C:$i]:
% 1.64/1.85     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.64/1.85       ( ![D:$i]:
% 1.64/1.85         ( ( r2_hidden @ D @ C ) <=>
% 1.64/1.85           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.64/1.85  thf('0', plain,
% 1.64/1.85      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.64/1.85         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 1.64/1.85          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 1.64/1.85          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 1.64/1.85      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.64/1.85  thf('1', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.64/1.85          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.64/1.85      inference('eq_fact', [status(thm)], ['0'])).
% 1.64/1.85  thf(d3_tarski, axiom,
% 1.64/1.85    (![A:$i,B:$i]:
% 1.64/1.85     ( ( r1_tarski @ A @ B ) <=>
% 1.64/1.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.64/1.85  thf('2', plain,
% 1.64/1.85      (![X3 : $i, X5 : $i]:
% 1.64/1.85         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.64/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.64/1.85  thf(t17_xboole_1, axiom,
% 1.64/1.85    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.64/1.85  thf('3', plain,
% 1.64/1.85      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 1.64/1.85      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.64/1.85  thf('4', plain,
% 1.64/1.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.64/1.85         (~ (r2_hidden @ X2 @ X3)
% 1.64/1.85          | (r2_hidden @ X2 @ X4)
% 1.64/1.85          | ~ (r1_tarski @ X3 @ X4))),
% 1.64/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.64/1.85  thf('5', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.85         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['3', '4'])).
% 1.64/1.85  thf('6', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.85         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.64/1.85          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 1.64/1.85      inference('sup-', [status(thm)], ['2', '5'])).
% 1.64/1.85  thf(t20_xboole_1, conjecture,
% 1.64/1.85    (![A:$i,B:$i,C:$i]:
% 1.64/1.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 1.64/1.85         ( ![D:$i]:
% 1.64/1.85           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 1.64/1.85             ( r1_tarski @ D @ A ) ) ) ) =>
% 1.64/1.85       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.64/1.85  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.85    (~( ![A:$i,B:$i,C:$i]:
% 1.64/1.85        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 1.64/1.85            ( ![D:$i]:
% 1.64/1.85              ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 1.64/1.85                ( r1_tarski @ D @ A ) ) ) ) =>
% 1.64/1.85          ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ) )),
% 1.64/1.85    inference('cnf.neg', [status(esa)], [t20_xboole_1])).
% 1.64/1.85  thf('7', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 1.64/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.85  thf('8', plain,
% 1.64/1.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.64/1.85         (~ (r2_hidden @ X2 @ X3)
% 1.64/1.85          | (r2_hidden @ X2 @ X4)
% 1.64/1.85          | ~ (r1_tarski @ X3 @ X4))),
% 1.64/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.64/1.85  thf('9', plain,
% 1.64/1.85      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.64/1.85      inference('sup-', [status(thm)], ['7', '8'])).
% 1.64/1.85  thf('10', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X1)
% 1.64/1.85          | (r2_hidden @ (sk_C @ X1 @ (k3_xboole_0 @ sk_A @ X0)) @ sk_C_1))),
% 1.64/1.85      inference('sup-', [status(thm)], ['6', '9'])).
% 1.64/1.85  thf('11', plain,
% 1.64/1.85      (![X3 : $i, X5 : $i]:
% 1.64/1.85         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.64/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.64/1.85  thf(commutativity_k3_xboole_0, axiom,
% 1.64/1.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.64/1.85  thf('12', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.64/1.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.64/1.85  thf('13', plain,
% 1.64/1.85      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 1.64/1.85      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.64/1.85  thf('14', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.64/1.85      inference('sup+', [status(thm)], ['12', '13'])).
% 1.64/1.85  thf('15', plain,
% 1.64/1.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.64/1.85         (~ (r2_hidden @ X2 @ X3)
% 1.64/1.85          | (r2_hidden @ X2 @ X4)
% 1.64/1.85          | ~ (r1_tarski @ X3 @ X4))),
% 1.64/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.64/1.85  thf('16', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.85         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['14', '15'])).
% 1.64/1.85  thf('17', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.85         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.64/1.85          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.64/1.85      inference('sup-', [status(thm)], ['11', '16'])).
% 1.64/1.85  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.64/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.85  thf('19', plain,
% 1.64/1.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.64/1.85         (~ (r2_hidden @ X2 @ X3)
% 1.64/1.85          | (r2_hidden @ X2 @ X4)
% 1.64/1.85          | ~ (r1_tarski @ X3 @ X4))),
% 1.64/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.64/1.85  thf('20', plain,
% 1.64/1.85      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.64/1.85      inference('sup-', [status(thm)], ['18', '19'])).
% 1.64/1.85  thf('21', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         ((r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ X1)
% 1.64/1.85          | (r2_hidden @ (sk_C @ X1 @ (k3_xboole_0 @ X0 @ sk_A)) @ sk_B))),
% 1.64/1.85      inference('sup-', [status(thm)], ['17', '20'])).
% 1.64/1.85  thf('22', plain,
% 1.64/1.85      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.64/1.85         (~ (r2_hidden @ X6 @ X7)
% 1.64/1.85          | ~ (r2_hidden @ X6 @ X8)
% 1.64/1.85          | (r2_hidden @ X6 @ X9)
% 1.64/1.85          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 1.64/1.85      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.64/1.85  thf('23', plain,
% 1.64/1.85      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.64/1.85         ((r2_hidden @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 1.64/1.85          | ~ (r2_hidden @ X6 @ X8)
% 1.64/1.85          | ~ (r2_hidden @ X6 @ X7))),
% 1.64/1.85      inference('simplify', [status(thm)], ['22'])).
% 1.64/1.85  thf('24', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.85         ((r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ X1)
% 1.64/1.85          | ~ (r2_hidden @ (sk_C @ X1 @ (k3_xboole_0 @ X0 @ sk_A)) @ X2)
% 1.64/1.85          | (r2_hidden @ (sk_C @ X1 @ (k3_xboole_0 @ X0 @ sk_A)) @ 
% 1.64/1.85             (k3_xboole_0 @ X2 @ sk_B)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['21', '23'])).
% 1.64/1.85  thf('25', plain,
% 1.64/1.85      (![X0 : $i]:
% 1.64/1.85         ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_A) @ X0)
% 1.64/1.85          | (r2_hidden @ (sk_C @ X0 @ (k3_xboole_0 @ sk_A @ sk_A)) @ 
% 1.64/1.85             (k3_xboole_0 @ sk_C_1 @ sk_B))
% 1.64/1.85          | (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_A) @ X0))),
% 1.64/1.85      inference('sup-', [status(thm)], ['10', '24'])).
% 1.64/1.85  thf('26', plain,
% 1.64/1.85      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.64/1.85         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 1.64/1.85          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 1.64/1.85          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 1.64/1.85      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.64/1.85  thf('27', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.64/1.85          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.64/1.85      inference('eq_fact', [status(thm)], ['26'])).
% 1.64/1.85  thf('28', plain,
% 1.64/1.85      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.64/1.85         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 1.64/1.85      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.64/1.85  thf('29', plain,
% 1.64/1.85      (![X0 : $i]:
% 1.64/1.85         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.64/1.85          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['27', '28'])).
% 1.64/1.85  thf('30', plain,
% 1.64/1.85      (![X0 : $i]:
% 1.64/1.85         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 1.64/1.85          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 1.64/1.85      inference('simplify', [status(thm)], ['29'])).
% 1.64/1.85  thf('31', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.64/1.85          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.64/1.85      inference('eq_fact', [status(thm)], ['0'])).
% 1.64/1.85  thf('32', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.64/1.85      inference('clc', [status(thm)], ['30', '31'])).
% 1.64/1.85  thf('33', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.64/1.85      inference('clc', [status(thm)], ['30', '31'])).
% 1.64/1.85  thf('34', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.64/1.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.64/1.85  thf('35', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.64/1.85      inference('clc', [status(thm)], ['30', '31'])).
% 1.64/1.85  thf('36', plain,
% 1.64/1.85      (![X0 : $i]:
% 1.64/1.85         ((r1_tarski @ sk_A @ X0)
% 1.64/1.85          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 1.64/1.85          | (r1_tarski @ sk_A @ X0))),
% 1.64/1.85      inference('demod', [status(thm)], ['25', '32', '33', '34', '35'])).
% 1.64/1.85  thf('37', plain,
% 1.64/1.85      (![X0 : $i]:
% 1.64/1.85         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 1.64/1.85          | (r1_tarski @ sk_A @ X0))),
% 1.64/1.85      inference('simplify', [status(thm)], ['36'])).
% 1.64/1.85  thf('38', plain,
% 1.64/1.85      (![X3 : $i, X5 : $i]:
% 1.64/1.85         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.64/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.64/1.85  thf('39', plain,
% 1.64/1.85      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 1.64/1.85        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['37', '38'])).
% 1.64/1.85  thf('40', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 1.64/1.85      inference('simplify', [status(thm)], ['39'])).
% 1.64/1.85  thf('41', plain,
% 1.64/1.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.64/1.85         (~ (r2_hidden @ X2 @ X3)
% 1.64/1.85          | (r2_hidden @ X2 @ X4)
% 1.64/1.85          | ~ (r1_tarski @ X3 @ X4))),
% 1.64/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.64/1.85  thf('42', plain,
% 1.64/1.85      (![X0 : $i]:
% 1.64/1.85         ((r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 1.64/1.85          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.64/1.85      inference('sup-', [status(thm)], ['40', '41'])).
% 1.64/1.85  thf('43', plain,
% 1.64/1.85      (![X0 : $i]:
% 1.64/1.85         (((sk_A) = (k3_xboole_0 @ X0 @ sk_A))
% 1.64/1.85          | (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ 
% 1.64/1.85             (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['1', '42'])).
% 1.64/1.85  thf('44', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.64/1.85          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.64/1.85      inference('eq_fact', [status(thm)], ['0'])).
% 1.64/1.85  thf('45', plain,
% 1.64/1.85      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.64/1.85         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 1.64/1.85      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.64/1.85  thf('46', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.64/1.85          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['44', '45'])).
% 1.64/1.85  thf('47', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.64/1.85          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.64/1.85      inference('simplify', [status(thm)], ['46'])).
% 1.64/1.85  thf('48', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.64/1.85          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.64/1.85      inference('eq_fact', [status(thm)], ['0'])).
% 1.64/1.85  thf('49', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.64/1.85      inference('clc', [status(thm)], ['47', '48'])).
% 1.64/1.85  thf('50', plain,
% 1.64/1.85      ((((sk_A) = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A))
% 1.64/1.85        | ((sk_A) = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['43', '49'])).
% 1.64/1.85  thf('51', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.64/1.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.64/1.85  thf('52', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.64/1.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.64/1.85  thf('53', plain,
% 1.64/1.85      ((((sk_A) = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))
% 1.64/1.85        | ((sk_A) = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))))),
% 1.64/1.85      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.64/1.85  thf('54', plain,
% 1.64/1.85      (((sk_A) = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 1.64/1.85      inference('simplify', [status(thm)], ['53'])).
% 1.64/1.85  thf('55', plain,
% 1.64/1.85      (![X7 : $i, X8 : $i, X11 : $i]:
% 1.64/1.85         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 1.64/1.85          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 1.64/1.85          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 1.64/1.85      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.64/1.85  thf('56', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.64/1.85      inference('sup+', [status(thm)], ['12', '13'])).
% 1.64/1.85  thf('57', plain,
% 1.64/1.85      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 1.64/1.85      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.64/1.85  thf('58', plain,
% 1.64/1.85      (![X14 : $i]:
% 1.64/1.85         ((r1_tarski @ X14 @ sk_A)
% 1.64/1.85          | ~ (r1_tarski @ X14 @ sk_C_1)
% 1.64/1.85          | ~ (r1_tarski @ X14 @ sk_B))),
% 1.64/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.85  thf('59', plain,
% 1.64/1.85      (![X0 : $i]:
% 1.64/1.85         (~ (r1_tarski @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)
% 1.64/1.85          | (r1_tarski @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_A))),
% 1.64/1.85      inference('sup-', [status(thm)], ['57', '58'])).
% 1.64/1.85  thf('60', plain, ((r1_tarski @ (k3_xboole_0 @ sk_C_1 @ sk_B) @ sk_A)),
% 1.64/1.85      inference('sup-', [status(thm)], ['56', '59'])).
% 1.64/1.85  thf('61', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.64/1.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.64/1.85  thf('62', plain, ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 1.64/1.85      inference('demod', [status(thm)], ['60', '61'])).
% 1.64/1.85  thf('63', plain,
% 1.64/1.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.64/1.85         (~ (r2_hidden @ X2 @ X3)
% 1.64/1.85          | (r2_hidden @ X2 @ X4)
% 1.64/1.85          | ~ (r1_tarski @ X3 @ X4))),
% 1.64/1.85      inference('cnf', [status(esa)], [d3_tarski])).
% 1.64/1.85  thf('64', plain,
% 1.64/1.85      (![X0 : $i]:
% 1.64/1.85         ((r2_hidden @ X0 @ sk_A)
% 1.64/1.85          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['62', '63'])).
% 1.64/1.85  thf('65', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X1 @ X0) @ X0)
% 1.64/1.85          | ((k3_xboole_0 @ sk_B @ sk_C_1) = (k3_xboole_0 @ X0 @ X1))
% 1.64/1.85          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X1 @ X0) @ 
% 1.64/1.85             sk_A))),
% 1.64/1.85      inference('sup-', [status(thm)], ['55', '64'])).
% 1.64/1.85  thf('66', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.64/1.85      inference('clc', [status(thm)], ['47', '48'])).
% 1.64/1.85  thf('67', plain,
% 1.64/1.85      ((((k3_xboole_0 @ sk_B @ sk_C_1)
% 1.64/1.85          = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))
% 1.64/1.85        | (r2_hidden @ 
% 1.64/1.85           (sk_D @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 1.64/1.85            (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.64/1.85           sk_A)
% 1.64/1.85        | ((k3_xboole_0 @ sk_B @ sk_C_1)
% 1.64/1.85            = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))))),
% 1.64/1.85      inference('sup-', [status(thm)], ['65', '66'])).
% 1.64/1.85  thf('68', plain,
% 1.64/1.85      (((sk_A) = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 1.64/1.85      inference('simplify', [status(thm)], ['53'])).
% 1.64/1.85  thf('69', plain,
% 1.64/1.85      (((sk_A) = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 1.64/1.85      inference('simplify', [status(thm)], ['53'])).
% 1.64/1.85  thf('70', plain,
% 1.64/1.85      ((((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_A))
% 1.64/1.85        | (r2_hidden @ 
% 1.64/1.85           (sk_D @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 1.64/1.85            (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.64/1.85           sk_A)
% 1.64/1.85        | ((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_A)))),
% 1.64/1.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.64/1.85  thf('71', plain,
% 1.64/1.85      (((r2_hidden @ 
% 1.64/1.85         (sk_D @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 1.64/1.85          (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.64/1.85         sk_A)
% 1.64/1.85        | ((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_A)))),
% 1.64/1.85      inference('simplify', [status(thm)], ['70'])).
% 1.64/1.85  thf('72', plain, (((sk_A) != (k3_xboole_0 @ sk_B @ sk_C_1))),
% 1.64/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.85  thf('73', plain,
% 1.64/1.85      ((r2_hidden @ 
% 1.64/1.85        (sk_D @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 1.64/1.85         (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 1.64/1.85        sk_A)),
% 1.64/1.85      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 1.64/1.85  thf('74', plain,
% 1.64/1.85      (![X0 : $i, X1 : $i]:
% 1.64/1.85         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.64/1.85          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.64/1.85      inference('clc', [status(thm)], ['47', '48'])).
% 1.64/1.85  thf('75', plain,
% 1.64/1.85      (((k3_xboole_0 @ sk_B @ sk_C_1)
% 1.64/1.85         = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 1.64/1.85      inference('sup-', [status(thm)], ['73', '74'])).
% 1.64/1.85  thf('76', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_A))),
% 1.64/1.85      inference('sup+', [status(thm)], ['54', '75'])).
% 1.64/1.85  thf('77', plain, (((sk_A) != (k3_xboole_0 @ sk_B @ sk_C_1))),
% 1.64/1.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.85  thf('78', plain, ($false),
% 1.64/1.85      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 1.64/1.85  
% 1.64/1.85  % SZS output end Refutation
% 1.64/1.85  
% 1.64/1.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
