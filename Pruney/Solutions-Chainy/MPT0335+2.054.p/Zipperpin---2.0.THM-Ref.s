%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uB0fUoxEG3

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:19 EST 2020

% Result     : Theorem 33.49s
% Output     : Refutation 33.49s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 933 expanded)
%              Number of leaves         :   15 ( 244 expanded)
%              Depth                    :   24
%              Number of atoms          : 1688 (12809 expanded)
%              Number of equality atoms :  107 ( 925 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('2',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X38: $i,X40: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X38 ) @ X40 )
      | ~ ( r2_hidden @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) )
      | ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) )
      | ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X2 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['36','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['29','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k1_tarski @ sk_D_1 ) )
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','46'])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('50',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('51',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('55',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ sk_C )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('60',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ sk_C )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k3_xboole_0 @ X4 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('70',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k3_xboole_0 @ X1 @ sk_A ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k3_xboole_0 @ X1 @ sk_A ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) )
      | ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) )
      | ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('85',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['29','45'])).

thf('88',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ) ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('90',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('91',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('92',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ sk_B )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('95',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ sk_B )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X3 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k3_xboole_0 @ X4 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('98',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('101',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('104',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('106',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','104','105'])).

thf('107',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['53','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uB0fUoxEG3
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:48:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 33.49/33.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 33.49/33.74  % Solved by: fo/fo7.sh
% 33.49/33.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 33.49/33.74  % done 8592 iterations in 33.269s
% 33.49/33.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 33.49/33.74  % SZS output start Refutation
% 33.49/33.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 33.49/33.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 33.49/33.74  thf(sk_D_1_type, type, sk_D_1: $i).
% 33.49/33.74  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 33.49/33.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 33.49/33.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 33.49/33.74  thf(sk_A_type, type, sk_A: $i).
% 33.49/33.74  thf(sk_B_type, type, sk_B: $i).
% 33.49/33.74  thf(sk_C_type, type, sk_C: $i).
% 33.49/33.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 33.49/33.74  thf(d4_xboole_0, axiom,
% 33.49/33.74    (![A:$i,B:$i,C:$i]:
% 33.49/33.74     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 33.49/33.74       ( ![D:$i]:
% 33.49/33.74         ( ( r2_hidden @ D @ C ) <=>
% 33.49/33.74           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 33.49/33.74  thf('0', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X5 : $i]:
% 33.49/33.74         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('1', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 33.49/33.74          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 33.49/33.74      inference('eq_fact', [status(thm)], ['0'])).
% 33.49/33.74  thf(t148_zfmisc_1, conjecture,
% 33.49/33.74    (![A:$i,B:$i,C:$i,D:$i]:
% 33.49/33.74     ( ( ( r1_tarski @ A @ B ) & 
% 33.49/33.74         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 33.49/33.74         ( r2_hidden @ D @ A ) ) =>
% 33.49/33.74       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 33.49/33.74  thf(zf_stmt_0, negated_conjecture,
% 33.49/33.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 33.49/33.74        ( ( ( r1_tarski @ A @ B ) & 
% 33.49/33.74            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 33.49/33.74            ( r2_hidden @ D @ A ) ) =>
% 33.49/33.74          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 33.49/33.74    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 33.49/33.74  thf('2', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 33.49/33.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.49/33.74  thf(l1_zfmisc_1, axiom,
% 33.49/33.74    (![A:$i,B:$i]:
% 33.49/33.74     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 33.49/33.74  thf('3', plain,
% 33.49/33.74      (![X38 : $i, X40 : $i]:
% 33.49/33.74         ((r1_tarski @ (k1_tarski @ X38) @ X40) | ~ (r2_hidden @ X38 @ X40))),
% 33.49/33.74      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 33.49/33.74  thf('4', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_A)),
% 33.49/33.74      inference('sup-', [status(thm)], ['2', '3'])).
% 33.49/33.74  thf(t28_xboole_1, axiom,
% 33.49/33.74    (![A:$i,B:$i]:
% 33.49/33.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 33.49/33.74  thf('5', plain,
% 33.49/33.74      (![X6 : $i, X7 : $i]:
% 33.49/33.74         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 33.49/33.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 33.49/33.74  thf('6', plain,
% 33.49/33.74      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_tarski @ sk_D_1))),
% 33.49/33.74      inference('sup-', [status(thm)], ['4', '5'])).
% 33.49/33.74  thf('7', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 33.49/33.74         (~ (r2_hidden @ X4 @ X3)
% 33.49/33.74          | (r2_hidden @ X4 @ X2)
% 33.49/33.74          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('8', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X4 : $i]:
% 33.49/33.74         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['7'])).
% 33.49/33.74  thf('9', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D_1)) | (r2_hidden @ X0 @ sk_A))),
% 33.49/33.74      inference('sup-', [status(thm)], ['6', '8'])).
% 33.49/33.74  thf('10', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))
% 33.49/33.74          | (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ sk_A))),
% 33.49/33.74      inference('sup-', [status(thm)], ['1', '9'])).
% 33.49/33.74  thf('11', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 33.49/33.74          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 33.49/33.74      inference('eq_fact', [status(thm)], ['0'])).
% 33.49/33.74  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D_1))),
% 33.49/33.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.49/33.74  thf('13', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X4 : $i]:
% 33.49/33.74         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['7'])).
% 33.49/33.74  thf('14', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D_1)) | (r2_hidden @ X0 @ sk_C))),
% 33.49/33.74      inference('sup-', [status(thm)], ['12', '13'])).
% 33.49/33.74  thf('15', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))
% 33.49/33.74          | (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ sk_C))),
% 33.49/33.74      inference('sup-', [status(thm)], ['11', '14'])).
% 33.49/33.74  thf('16', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 33.49/33.74         (~ (r2_hidden @ X0 @ X1)
% 33.49/33.74          | ~ (r2_hidden @ X0 @ X2)
% 33.49/33.74          | (r2_hidden @ X0 @ X3)
% 33.49/33.74          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('17', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.49/33.74         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | ~ (r2_hidden @ X0 @ X2)
% 33.49/33.74          | ~ (r2_hidden @ X0 @ X1))),
% 33.49/33.74      inference('simplify', [status(thm)], ['16'])).
% 33.49/33.74  thf('18', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))
% 33.49/33.74          | ~ (r2_hidden @ 
% 33.49/33.74               (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ X1)
% 33.49/33.74          | (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ 
% 33.49/33.74             (k3_xboole_0 @ X1 @ sk_C)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['15', '17'])).
% 33.49/33.74  thf('19', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))
% 33.49/33.74          | (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ 
% 33.49/33.74             (k3_xboole_0 @ sk_A @ sk_C))
% 33.49/33.74          | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1))))),
% 33.49/33.74      inference('sup-', [status(thm)], ['10', '18'])).
% 33.49/33.74  thf('20', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         ((r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ 
% 33.49/33.74           (k3_xboole_0 @ sk_A @ sk_C))
% 33.49/33.74          | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1))))),
% 33.49/33.74      inference('simplify', [status(thm)], ['19'])).
% 33.49/33.74  thf('21', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 33.49/33.74          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 33.49/33.74      inference('eq_fact', [status(thm)], ['0'])).
% 33.49/33.74  thf('22', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X5 : $i]:
% 33.49/33.74         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('23', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 33.49/33.74          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['21', '22'])).
% 33.49/33.74  thf('24', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 33.49/33.74          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['23'])).
% 33.49/33.74  thf('25', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 33.49/33.74          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 33.49/33.74      inference('eq_fact', [status(thm)], ['0'])).
% 33.49/33.74  thf('26', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 33.49/33.74      inference('clc', [status(thm)], ['24', '25'])).
% 33.49/33.74  thf('27', plain,
% 33.49/33.74      ((((k1_tarski @ sk_D_1)
% 33.49/33.74          = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ (k1_tarski @ sk_D_1)))
% 33.49/33.74        | ((k1_tarski @ sk_D_1)
% 33.49/33.74            = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ (k1_tarski @ sk_D_1))))),
% 33.49/33.74      inference('sup-', [status(thm)], ['20', '26'])).
% 33.49/33.74  thf('28', plain,
% 33.49/33.74      (((k1_tarski @ sk_D_1)
% 33.49/33.74         = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['27'])).
% 33.49/33.74  thf(t48_xboole_1, axiom,
% 33.49/33.74    (![A:$i,B:$i]:
% 33.49/33.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 33.49/33.74  thf('29', plain,
% 33.49/33.74      (![X8 : $i, X9 : $i]:
% 33.49/33.74         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 33.49/33.74           = (k3_xboole_0 @ X8 @ X9))),
% 33.49/33.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.49/33.74  thf('30', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X5 : $i]:
% 33.49/33.74         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('31', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 33.49/33.74         (~ (r2_hidden @ X4 @ X3)
% 33.49/33.74          | (r2_hidden @ X4 @ X1)
% 33.49/33.74          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('32', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X4 : $i]:
% 33.49/33.74         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['31'])).
% 33.49/33.74  thf('33', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X2)
% 33.49/33.74          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X2 @ X3))
% 33.49/33.74          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X1))),
% 33.49/33.74      inference('sup-', [status(thm)], ['30', '32'])).
% 33.49/33.74  thf('34', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X1 @ X0) @ X0)
% 33.49/33.74          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X0 @ X1)))),
% 33.49/33.74      inference('eq_fact', [status(thm)], ['33'])).
% 33.49/33.74  thf('35', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X5 : $i]:
% 33.49/33.74         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('36', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X0 @ X0))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X0) @ 
% 33.49/33.74               (k3_xboole_0 @ X0 @ X1))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X0) @ X0)
% 33.49/33.74          | ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X0 @ X0)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['34', '35'])).
% 33.49/33.74  thf('37', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 33.49/33.74          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 33.49/33.74      inference('eq_fact', [status(thm)], ['0'])).
% 33.49/33.74  thf('38', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 33.49/33.74      inference('clc', [status(thm)], ['24', '25'])).
% 33.49/33.74  thf('39', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['37', '38'])).
% 33.49/33.74  thf('40', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 33.49/33.74      inference('simplify', [status(thm)], ['39'])).
% 33.49/33.74  thf('41', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 33.49/33.74      inference('simplify', [status(thm)], ['39'])).
% 33.49/33.74  thf('42', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (((k3_xboole_0 @ X0 @ X1) = (X0))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X0) @ 
% 33.49/33.74               (k3_xboole_0 @ X0 @ X1))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X0) @ X0)
% 33.49/33.74          | ((k3_xboole_0 @ X0 @ X1) = (X0)))),
% 33.49/33.74      inference('demod', [status(thm)], ['36', '40', '41'])).
% 33.49/33.74  thf('43', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X0) @ X0)
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X0) @ 
% 33.49/33.74               (k3_xboole_0 @ X0 @ X1))
% 33.49/33.74          | ((k3_xboole_0 @ X0 @ X1) = (X0)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['42'])).
% 33.49/33.74  thf('44', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X4 : $i]:
% 33.49/33.74         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['31'])).
% 33.49/33.74  thf('45', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (((k3_xboole_0 @ X0 @ X1) = (X0))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X0) @ 
% 33.49/33.74               (k3_xboole_0 @ X0 @ X1)))),
% 33.49/33.74      inference('clc', [status(thm)], ['43', '44'])).
% 33.49/33.74  thf('46', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (~ (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X1 @ X1) @ 
% 33.49/33.74             (k3_xboole_0 @ X1 @ X0))
% 33.49/33.74          | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['29', '45'])).
% 33.49/33.74  thf('47', plain,
% 33.49/33.74      ((~ (r2_hidden @ 
% 33.49/33.74           (sk_D @ 
% 33.49/33.74            (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74             (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ (k1_tarski @ sk_D_1))) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_A @ sk_C) @ (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ (k1_tarski @ sk_D_1))
% 33.49/33.74            = (k3_xboole_0 @ sk_A @ sk_C)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['28', '46'])).
% 33.49/33.74  thf('48', plain,
% 33.49/33.74      (![X8 : $i, X9 : $i]:
% 33.49/33.74         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 33.49/33.74           = (k3_xboole_0 @ X8 @ X9))),
% 33.49/33.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.49/33.74  thf('49', plain,
% 33.49/33.74      (((k1_tarski @ sk_D_1)
% 33.49/33.74         = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['27'])).
% 33.49/33.74  thf('50', plain,
% 33.49/33.74      (((k1_tarski @ sk_D_1)
% 33.49/33.74         = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['27'])).
% 33.49/33.74  thf('51', plain,
% 33.49/33.74      ((~ (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ sk_C)))),
% 33.49/33.74      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 33.49/33.74  thf('52', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D_1))),
% 33.49/33.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.49/33.74  thf('53', plain,
% 33.49/33.74      (~ (r2_hidden @ 
% 33.49/33.74          (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74           (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74          (k1_tarski @ sk_D_1))),
% 33.49/33.74      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 33.49/33.74  thf('54', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X5 : $i]:
% 33.49/33.74         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('55', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X4 : $i]:
% 33.49/33.74         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['7'])).
% 33.49/33.74  thf('56', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 33.49/33.74          | ((X3) = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 33.49/33.74      inference('sup-', [status(thm)], ['54', '55'])).
% 33.49/33.74  thf('57', plain,
% 33.49/33.74      (~ (r2_hidden @ 
% 33.49/33.74          (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74           (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74          (k1_tarski @ sk_D_1))),
% 33.49/33.74      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 33.49/33.74  thf('58', plain,
% 33.49/33.74      (((r2_hidden @ 
% 33.49/33.74         (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74          (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74         sk_C)
% 33.49/33.74        | ((k1_tarski @ sk_D_1)
% 33.49/33.74            = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74               (k3_xboole_0 @ sk_A @ sk_C))))),
% 33.49/33.74      inference('sup-', [status(thm)], ['56', '57'])).
% 33.49/33.74  thf('59', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 33.49/33.74      inference('simplify', [status(thm)], ['39'])).
% 33.49/33.74  thf('60', plain,
% 33.49/33.74      (((r2_hidden @ 
% 33.49/33.74         (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74          (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74         sk_C)
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ sk_C)))),
% 33.49/33.74      inference('demod', [status(thm)], ['58', '59'])).
% 33.49/33.74  thf('61', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D_1))),
% 33.49/33.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.49/33.74  thf('62', plain,
% 33.49/33.74      ((r2_hidden @ 
% 33.49/33.74        (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74         (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74        sk_C)),
% 33.49/33.74      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 33.49/33.74  thf('63', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X5 : $i]:
% 33.49/33.74         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('64', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X4 : $i]:
% 33.49/33.74         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['31'])).
% 33.49/33.74  thf('65', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X3)
% 33.49/33.74          | ((X3) = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 33.49/33.74      inference('sup-', [status(thm)], ['63', '64'])).
% 33.49/33.74  thf('66', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.49/33.74         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | ~ (r2_hidden @ X0 @ X2)
% 33.49/33.74          | ~ (r2_hidden @ X0 @ X1))),
% 33.49/33.74      inference('simplify', [status(thm)], ['16'])).
% 33.49/33.74  thf('67', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 33.49/33.74         (((X3) = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ X3)
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ X4)
% 33.49/33.74          | (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ 
% 33.49/33.74             (k3_xboole_0 @ X4 @ X0)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['65', '66'])).
% 33.49/33.74  thf('68', plain,
% 33.49/33.74      (((r2_hidden @ 
% 33.49/33.74         (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74          (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74         (k3_xboole_0 @ sk_C @ sk_A))
% 33.49/33.74        | (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k1_tarski @ sk_D_1)
% 33.49/33.74            = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74               (k3_xboole_0 @ sk_A @ sk_C))))),
% 33.49/33.74      inference('sup-', [status(thm)], ['62', '67'])).
% 33.49/33.74  thf('69', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X5 : $i]:
% 33.49/33.74         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 33.49/33.74          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 33.49/33.74      inference('cnf', [status(esa)], [d4_xboole_0])).
% 33.49/33.74  thf('70', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X4 : $i]:
% 33.49/33.74         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['7'])).
% 33.49/33.74  thf('71', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 33.49/33.74         ((r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X3)
% 33.49/33.74          | ((X3) = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 33.49/33.74      inference('sup-', [status(thm)], ['69', '70'])).
% 33.49/33.74  thf('72', plain, ((r1_tarski @ sk_A @ sk_B)),
% 33.49/33.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.49/33.74  thf('73', plain,
% 33.49/33.74      (![X6 : $i, X7 : $i]:
% 33.49/33.74         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 33.49/33.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 33.49/33.74  thf('74', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 33.49/33.74      inference('sup-', [status(thm)], ['72', '73'])).
% 33.49/33.74  thf('75', plain,
% 33.49/33.74      (![X1 : $i, X2 : $i, X4 : $i]:
% 33.49/33.74         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['7'])).
% 33.49/33.74  thf('76', plain,
% 33.49/33.74      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 33.49/33.74      inference('sup-', [status(thm)], ['74', '75'])).
% 33.49/33.74  thf('77', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.49/33.74         (((X2) = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ sk_A)))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X2 @ (k3_xboole_0 @ X1 @ sk_A) @ X0) @ X2)
% 33.49/33.74          | (r2_hidden @ (sk_D @ X2 @ (k3_xboole_0 @ X1 @ sk_A) @ X0) @ sk_B))),
% 33.49/33.74      inference('sup-', [status(thm)], ['71', '76'])).
% 33.49/33.74  thf('78', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))
% 33.49/33.74          | (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ sk_C))),
% 33.49/33.74      inference('sup-', [status(thm)], ['11', '14'])).
% 33.49/33.74  thf('79', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))
% 33.49/33.74          | (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ sk_A))),
% 33.49/33.74      inference('sup-', [status(thm)], ['1', '9'])).
% 33.49/33.74  thf('80', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.49/33.74         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 33.49/33.74          | ~ (r2_hidden @ X0 @ X2)
% 33.49/33.74          | ~ (r2_hidden @ X0 @ X1))),
% 33.49/33.74      inference('simplify', [status(thm)], ['16'])).
% 33.49/33.74  thf('81', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))
% 33.49/33.74          | ~ (r2_hidden @ 
% 33.49/33.74               (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ X1)
% 33.49/33.74          | (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ 
% 33.49/33.74             (k3_xboole_0 @ X1 @ sk_A)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['79', '80'])).
% 33.49/33.74  thf('82', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))
% 33.49/33.74          | (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ 
% 33.49/33.74             (k3_xboole_0 @ sk_C @ sk_A))
% 33.49/33.74          | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1))))),
% 33.49/33.74      inference('sup-', [status(thm)], ['78', '81'])).
% 33.49/33.74  thf('83', plain,
% 33.49/33.74      (![X0 : $i]:
% 33.49/33.74         ((r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ 
% 33.49/33.74           (k3_xboole_0 @ sk_C @ sk_A))
% 33.49/33.74          | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1))))),
% 33.49/33.74      inference('simplify', [status(thm)], ['82'])).
% 33.49/33.74  thf('84', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 33.49/33.74      inference('clc', [status(thm)], ['24', '25'])).
% 33.49/33.74  thf('85', plain,
% 33.49/33.74      ((((k1_tarski @ sk_D_1)
% 33.49/33.74          = (k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D_1)))
% 33.49/33.74        | ((k1_tarski @ sk_D_1)
% 33.49/33.74            = (k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D_1))))),
% 33.49/33.74      inference('sup-', [status(thm)], ['83', '84'])).
% 33.49/33.74  thf('86', plain,
% 33.49/33.74      (((k1_tarski @ sk_D_1)
% 33.49/33.74         = (k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D_1)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['85'])).
% 33.49/33.74  thf('87', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i]:
% 33.49/33.74         (~ (r2_hidden @ 
% 33.49/33.74             (sk_D @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X1 @ X1) @ 
% 33.49/33.74             (k3_xboole_0 @ X1 @ X0))
% 33.49/33.74          | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['29', '45'])).
% 33.49/33.74  thf('88', plain,
% 33.49/33.74      ((~ (r2_hidden @ 
% 33.49/33.74           (sk_D @ 
% 33.49/33.74            (k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74             (k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D_1))) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_C @ sk_A) @ (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D_1))
% 33.49/33.74            = (k3_xboole_0 @ sk_C @ sk_A)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['86', '87'])).
% 33.49/33.74  thf('89', plain,
% 33.49/33.74      (![X8 : $i, X9 : $i]:
% 33.49/33.74         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 33.49/33.74           = (k3_xboole_0 @ X8 @ X9))),
% 33.49/33.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 33.49/33.74  thf('90', plain,
% 33.49/33.74      (((k1_tarski @ sk_D_1)
% 33.49/33.74         = (k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D_1)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['85'])).
% 33.49/33.74  thf('91', plain,
% 33.49/33.74      (((k1_tarski @ sk_D_1)
% 33.49/33.74         = (k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D_1)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['85'])).
% 33.49/33.74  thf('92', plain,
% 33.49/33.74      ((~ (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 33.49/33.74      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 33.49/33.74  thf('93', plain,
% 33.49/33.74      (((r2_hidden @ 
% 33.49/33.74         (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74          (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74         sk_B)
% 33.49/33.74        | ((k1_tarski @ sk_D_1)
% 33.49/33.74            = (k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74               (k3_xboole_0 @ sk_C @ sk_A)))
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['77', '92'])).
% 33.49/33.74  thf('94', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 33.49/33.74      inference('simplify', [status(thm)], ['39'])).
% 33.49/33.74  thf('95', plain,
% 33.49/33.74      (((r2_hidden @ 
% 33.49/33.74         (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74          (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74         sk_B)
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A))
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 33.49/33.74      inference('demod', [status(thm)], ['93', '94'])).
% 33.49/33.74  thf('96', plain,
% 33.49/33.74      ((((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A))
% 33.49/33.74        | (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74           sk_B))),
% 33.49/33.74      inference('simplify', [status(thm)], ['95'])).
% 33.49/33.74  thf('97', plain,
% 33.49/33.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 33.49/33.74         (((X3) = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))
% 33.49/33.74          | (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ X3)
% 33.49/33.74          | ~ (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ X4)
% 33.49/33.74          | (r2_hidden @ (sk_D @ X3 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ 
% 33.49/33.74             (k3_xboole_0 @ X4 @ X0)))),
% 33.49/33.74      inference('sup-', [status(thm)], ['65', '66'])).
% 33.49/33.74  thf('98', plain,
% 33.49/33.74      ((((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A))
% 33.49/33.74        | (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74           (k3_xboole_0 @ sk_B @ sk_C))
% 33.49/33.74        | (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k1_tarski @ sk_D_1)
% 33.49/33.74            = (k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74               (k3_xboole_0 @ sk_C @ sk_A))))),
% 33.49/33.74      inference('sup-', [status(thm)], ['96', '97'])).
% 33.49/33.74  thf('99', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D_1))),
% 33.49/33.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.49/33.74  thf('100', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 33.49/33.74      inference('simplify', [status(thm)], ['39'])).
% 33.49/33.74  thf('101', plain,
% 33.49/33.74      ((((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A))
% 33.49/33.74        | (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 33.49/33.74      inference('demod', [status(thm)], ['98', '99', '100'])).
% 33.49/33.74  thf('102', plain,
% 33.49/33.74      (((r2_hidden @ 
% 33.49/33.74         (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74          (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74         (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['101'])).
% 33.49/33.74  thf('103', plain,
% 33.49/33.74      ((~ (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 33.49/33.74      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 33.49/33.74  thf('104', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A))),
% 33.49/33.74      inference('clc', [status(thm)], ['102', '103'])).
% 33.49/33.74  thf('105', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 33.49/33.74      inference('simplify', [status(thm)], ['39'])).
% 33.49/33.74  thf('106', plain,
% 33.49/33.74      (((r2_hidden @ 
% 33.49/33.74         (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74          (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74         (k1_tarski @ sk_D_1))
% 33.49/33.74        | (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1))
% 33.49/33.74        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ sk_C)))),
% 33.49/33.74      inference('demod', [status(thm)], ['68', '104', '105'])).
% 33.49/33.74  thf('107', plain,
% 33.49/33.74      ((((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ sk_C))
% 33.49/33.74        | (r2_hidden @ 
% 33.49/33.74           (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74            (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74           (k1_tarski @ sk_D_1)))),
% 33.49/33.74      inference('simplify', [status(thm)], ['106'])).
% 33.49/33.74  thf('108', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D_1))),
% 33.49/33.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.49/33.74  thf('109', plain,
% 33.49/33.74      ((r2_hidden @ 
% 33.49/33.74        (sk_D @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 33.49/33.74         (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 33.49/33.74        (k1_tarski @ sk_D_1))),
% 33.49/33.74      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 33.49/33.74  thf('110', plain, ($false), inference('demod', [status(thm)], ['53', '109'])).
% 33.49/33.74  
% 33.49/33.74  % SZS output end Refutation
% 33.49/33.74  
% 33.49/33.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
