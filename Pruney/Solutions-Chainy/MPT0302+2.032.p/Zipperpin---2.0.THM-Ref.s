%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KjTmC33D3p

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:09 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 391 expanded)
%              Number of leaves         :   13 ( 110 expanded)
%              Depth                    :   20
%              Number of atoms          : 1193 (5353 expanded)
%              Number of equality atoms :   96 ( 465 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X11 ) )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('6',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

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
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X2 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X2 @ X0 )
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
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['36','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ X1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['29','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_B_1 ) @ sk_A )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','51'])).

thf('53',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('54',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('55',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 ) @ sk_A )
    | ( sk_A = sk_B_1 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('60',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ X1 ) @ X1 )
      | ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
        = X1 ) ) ),
    inference('sup+',[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ X1 ) @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 ) @ sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['58','68'])).

thf('70',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('71',plain,
    ( ( r2_hidden @ ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 ) @ sk_B_1 )
    | ( sk_A = sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r2_hidden @ ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X11 ) )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','85'])).

thf('87',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('90',plain,(
    r2_hidden @ ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['57','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KjTmC33D3p
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.16  % Solved by: fo/fo7.sh
% 0.91/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.16  % done 1053 iterations in 0.729s
% 0.91/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.16  % SZS output start Refutation
% 0.91/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.16  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.16  thf(sk_B_type, type, sk_B: $i > $i).
% 0.91/1.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.16  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.91/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.16  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.91/1.16  thf(d4_xboole_0, axiom,
% 0.91/1.16    (![A:$i,B:$i,C:$i]:
% 0.91/1.16     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.91/1.16       ( ![D:$i]:
% 0.91/1.16         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.16           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.91/1.16  thf('0', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.16         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.91/1.16          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.91/1.16          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('1', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['0'])).
% 0.91/1.16  thf(t7_xboole_0, axiom,
% 0.91/1.16    (![A:$i]:
% 0.91/1.16     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.91/1.16          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.91/1.16  thf('2', plain,
% 0.91/1.16      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.91/1.16      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.91/1.16  thf(l54_zfmisc_1, axiom,
% 0.91/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.16     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.91/1.16       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.91/1.16  thf('3', plain,
% 0.91/1.16      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.91/1.16         ((r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X11))
% 0.91/1.16          | ~ (r2_hidden @ X9 @ X11)
% 0.91/1.16          | ~ (r2_hidden @ X7 @ X8))),
% 0.91/1.16      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.16  thf('4', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.16         (((X0) = (k1_xboole_0))
% 0.91/1.16          | ~ (r2_hidden @ X2 @ X1)
% 0.91/1.16          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.91/1.16             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.16  thf('5', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.16         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | (r2_hidden @ (k4_tarski @ (sk_D @ X0 @ X0 @ X1) @ (sk_B @ X2)) @ 
% 0.91/1.16             (k2_zfmisc_1 @ X0 @ X2))
% 0.91/1.16          | ((X2) = (k1_xboole_0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['1', '4'])).
% 0.91/1.16  thf(t114_zfmisc_1, conjecture,
% 0.91/1.16    (![A:$i,B:$i]:
% 0.91/1.16     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.91/1.16       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.91/1.16         ( ( A ) = ( B ) ) ) ))).
% 0.91/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.16    (~( ![A:$i,B:$i]:
% 0.91/1.16        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.91/1.16          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.91/1.16            ( ( A ) = ( B ) ) ) ) )),
% 0.91/1.16    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.91/1.16  thf('6', plain,
% 0.91/1.16      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('7', plain,
% 0.91/1.16      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.16         ((r2_hidden @ X7 @ X8)
% 0.91/1.16          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.91/1.16      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.16  thf('8', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.91/1.16          | (r2_hidden @ X1 @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.16  thf('9', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((sk_B_1) = (k1_xboole_0))
% 0.91/1.16          | ((sk_A) = (k3_xboole_0 @ X0 @ sk_A))
% 0.91/1.16          | (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ sk_B_1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['5', '8'])).
% 0.91/1.16  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('11', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((sk_A) = (k3_xboole_0 @ X0 @ sk_A))
% 0.91/1.16          | (r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ sk_B_1))),
% 0.91/1.16      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.91/1.16  thf('12', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['0'])).
% 0.91/1.16  thf('13', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.16         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('14', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['12', '13'])).
% 0.91/1.16  thf('15', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['14'])).
% 0.91/1.16  thf('16', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['0'])).
% 0.91/1.16  thf('17', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.91/1.16      inference('clc', [status(thm)], ['15', '16'])).
% 0.91/1.16  thf('18', plain,
% 0.91/1.16      ((((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.91/1.16        | ((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['11', '17'])).
% 0.91/1.16  thf('19', plain, (((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('simplify', [status(thm)], ['18'])).
% 0.91/1.16  thf('20', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.16         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.91/1.16          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.91/1.16          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('21', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['20'])).
% 0.91/1.16  thf('22', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X4 @ X3)
% 0.91/1.16          | (r2_hidden @ X4 @ X1)
% 0.91/1.16          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('23', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.16         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['22'])).
% 0.91/1.16  thf('24', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.16         (((k3_xboole_0 @ X1 @ X0)
% 0.91/1.16            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 0.91/1.16          | (r2_hidden @ 
% 0.91/1.16             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.91/1.16             X1))),
% 0.91/1.16      inference('sup-', [status(thm)], ['21', '23'])).
% 0.91/1.16  thf('25', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.16         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('26', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((k3_xboole_0 @ X0 @ X1)
% 0.91/1.16            = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))
% 0.91/1.16          | ~ (r2_hidden @ 
% 0.91/1.16               (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.91/1.16               (k3_xboole_0 @ X0 @ X1))
% 0.91/1.16          | ~ (r2_hidden @ 
% 0.91/1.16               (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.91/1.16               (k3_xboole_0 @ X0 @ X1))
% 0.91/1.16          | ((k3_xboole_0 @ X0 @ X1)
% 0.91/1.16              = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['24', '25'])).
% 0.91/1.16  thf('27', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ 
% 0.91/1.16             (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.91/1.16             (k3_xboole_0 @ X0 @ X1))
% 0.91/1.16          | ((k3_xboole_0 @ X0 @ X1)
% 0.91/1.16              = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['26'])).
% 0.91/1.16  thf('28', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['20'])).
% 0.91/1.16  thf('29', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((k3_xboole_0 @ X0 @ X1)
% 0.91/1.16           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.91/1.16      inference('clc', [status(thm)], ['27', '28'])).
% 0.91/1.16  thf('30', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.16         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.91/1.16          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.91/1.16          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('31', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X4 @ X3)
% 0.91/1.16          | (r2_hidden @ X4 @ X2)
% 0.91/1.16          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('32', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.16         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['31'])).
% 0.91/1.16  thf('33', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X2)
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X2 @ X3))
% 0.91/1.16          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X0))),
% 0.91/1.16      inference('sup-', [status(thm)], ['30', '32'])).
% 0.91/1.16  thf('34', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X2 @ X0) @ X1 @ X0) @ X0)
% 0.91/1.16          | ((k3_xboole_0 @ X2 @ X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['33'])).
% 0.91/1.16  thf('35', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.16         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('36', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ 
% 0.91/1.16               (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ X0)
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.16  thf('37', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['20'])).
% 0.91/1.16  thf('38', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.16         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('39', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.16  thf('40', plain,
% 0.91/1.16      (![X0 : $i]:
% 0.91/1.16         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['39'])).
% 0.91/1.16  thf('41', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.91/1.16          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('eq_fact', [status(thm)], ['0'])).
% 0.91/1.16  thf('42', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.16      inference('clc', [status(thm)], ['40', '41'])).
% 0.91/1.16  thf('43', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.16      inference('clc', [status(thm)], ['40', '41'])).
% 0.91/1.16  thf('44', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((k3_xboole_0 @ X1 @ X0) = (X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ 
% 0.91/1.16               (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ X0)
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (X0)))),
% 0.91/1.16      inference('demod', [status(thm)], ['36', '42', '43'])).
% 0.91/1.16  thf('45', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ X0)
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ 
% 0.91/1.16               (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (X0)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['44'])).
% 0.91/1.16  thf('46', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.16         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.91/1.16      inference('simplify', [status(thm)], ['31'])).
% 0.91/1.16  thf('47', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((k3_xboole_0 @ X1 @ X0) = (X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ 
% 0.91/1.16               (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('clc', [status(thm)], ['45', '46'])).
% 0.91/1.16  thf('48', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ 
% 0.91/1.16             (sk_D @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ X1 @ X1) @ 
% 0.91/1.16             (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['29', '47'])).
% 0.91/1.16  thf('49', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((k3_xboole_0 @ X0 @ X1)
% 0.91/1.16           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.91/1.16      inference('clc', [status(thm)], ['27', '28'])).
% 0.91/1.16  thf('50', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((k3_xboole_0 @ X0 @ X1)
% 0.91/1.16           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.91/1.16      inference('clc', [status(thm)], ['27', '28'])).
% 0.91/1.16  thf('51', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ X1) @ 
% 0.91/1.16             (k3_xboole_0 @ X1 @ X0))
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.91/1.16  thf('52', plain,
% 0.91/1.16      ((~ (r2_hidden @ 
% 0.91/1.16           (sk_D @ (k3_xboole_0 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_B_1) @ sk_A)
% 0.91/1.16        | ((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['19', '51'])).
% 0.91/1.16  thf('53', plain, (((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('simplify', [status(thm)], ['18'])).
% 0.91/1.16  thf('54', plain, (((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('simplify', [status(thm)], ['18'])).
% 0.91/1.16  thf('55', plain,
% 0.91/1.16      ((~ (r2_hidden @ (sk_D @ sk_A @ sk_B_1 @ sk_B_1) @ sk_A)
% 0.91/1.16        | ((sk_A) = (sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.91/1.16  thf('56', plain, (((sk_A) != (sk_B_1))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('57', plain, (~ (r2_hidden @ (sk_D @ sk_A @ sk_B_1 @ sk_B_1) @ sk_A)),
% 0.91/1.16      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.91/1.16  thf('58', plain, (((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('simplify', [status(thm)], ['18'])).
% 0.91/1.16  thf('59', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((k3_xboole_0 @ X0 @ X1)
% 0.91/1.16           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.91/1.16      inference('clc', [status(thm)], ['27', '28'])).
% 0.91/1.16  thf('60', plain,
% 0.91/1.16      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.91/1.16         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.91/1.16          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.91/1.16          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.91/1.16      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.16  thf('61', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((k3_xboole_0 @ X1 @ X0) = (X0))
% 0.91/1.16          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ 
% 0.91/1.16               (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.16      inference('clc', [status(thm)], ['45', '46'])).
% 0.91/1.16  thf('62', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ X0)
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X0))
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['60', '61'])).
% 0.91/1.16  thf('63', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.16      inference('clc', [status(thm)], ['40', '41'])).
% 0.91/1.16  thf('64', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ X0)
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (X0))
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (X0)))),
% 0.91/1.16      inference('demod', [status(thm)], ['62', '63'])).
% 0.91/1.16  thf('65', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((k3_xboole_0 @ X1 @ X0) = (X0))
% 0.91/1.16          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X0 @ X0) @ X0))),
% 0.91/1.16      inference('simplify', [status(thm)], ['64'])).
% 0.91/1.16  thf('66', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ X1) @ X1)
% 0.91/1.16          | ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1)))),
% 0.91/1.16      inference('sup+', [status(thm)], ['59', '65'])).
% 0.91/1.16  thf('67', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((k3_xboole_0 @ X0 @ X1)
% 0.91/1.16           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.91/1.16      inference('clc', [status(thm)], ['27', '28'])).
% 0.91/1.16  thf('68', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ X1) @ X1)
% 0.91/1.16          | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['66', '67'])).
% 0.91/1.16  thf('69', plain,
% 0.91/1.16      (((r2_hidden @ (sk_D @ sk_A @ sk_B_1 @ sk_B_1) @ sk_B_1)
% 0.91/1.16        | ((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1)))),
% 0.91/1.16      inference('sup+', [status(thm)], ['58', '68'])).
% 0.91/1.16  thf('70', plain, (((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('simplify', [status(thm)], ['18'])).
% 0.91/1.16  thf('71', plain,
% 0.91/1.16      (((r2_hidden @ (sk_D @ sk_A @ sk_B_1 @ sk_B_1) @ sk_B_1)
% 0.91/1.16        | ((sk_A) = (sk_B_1)))),
% 0.91/1.16      inference('demod', [status(thm)], ['69', '70'])).
% 0.91/1.16  thf('72', plain, (((sk_A) != (sk_B_1))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('73', plain, ((r2_hidden @ (sk_D @ sk_A @ sk_B_1 @ sk_B_1) @ sk_B_1)),
% 0.91/1.16      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.91/1.16  thf('74', plain,
% 0.91/1.16      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.91/1.16      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.91/1.16  thf('75', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.16         (((X0) = (k1_xboole_0))
% 0.91/1.16          | ~ (r2_hidden @ X2 @ X1)
% 0.91/1.16          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.91/1.16             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.16  thf('76', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (((X0) = (k1_xboole_0))
% 0.91/1.16          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.91/1.16             (k2_zfmisc_1 @ X0 @ X1))
% 0.91/1.16          | ((X1) = (k1_xboole_0)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['74', '75'])).
% 0.91/1.16  thf('77', plain,
% 0.91/1.16      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('78', plain,
% 0.91/1.16      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.16         ((r2_hidden @ X9 @ X10)
% 0.91/1.16          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.91/1.16      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.16  thf('79', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.91/1.16          | (r2_hidden @ X0 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['77', '78'])).
% 0.91/1.16  thf('80', plain,
% 0.91/1.16      ((((sk_B_1) = (k1_xboole_0))
% 0.91/1.16        | ((sk_A) = (k1_xboole_0))
% 0.91/1.16        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['76', '79'])).
% 0.91/1.16  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('82', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('83', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 0.91/1.16      inference('simplify_reflect-', [status(thm)], ['80', '81', '82'])).
% 0.91/1.16  thf('84', plain,
% 0.91/1.16      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.91/1.16         ((r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X11))
% 0.91/1.16          | ~ (r2_hidden @ X9 @ X11)
% 0.91/1.16          | ~ (r2_hidden @ X7 @ X8))),
% 0.91/1.16      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.16  thf('85', plain,
% 0.91/1.16      (![X0 : $i, X1 : $i]:
% 0.91/1.16         (~ (r2_hidden @ X1 @ X0)
% 0.91/1.16          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ sk_B_1)) @ 
% 0.91/1.16             (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.91/1.16      inference('sup-', [status(thm)], ['83', '84'])).
% 0.91/1.16  thf('86', plain,
% 0.91/1.16      ((r2_hidden @ 
% 0.91/1.16        (k4_tarski @ (sk_D @ sk_A @ sk_B_1 @ sk_B_1) @ (sk_B @ sk_B_1)) @ 
% 0.91/1.16        (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('sup-', [status(thm)], ['73', '85'])).
% 0.91/1.16  thf('87', plain,
% 0.91/1.16      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.91/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.16  thf('88', plain,
% 0.91/1.16      ((r2_hidden @ 
% 0.91/1.16        (k4_tarski @ (sk_D @ sk_A @ sk_B_1 @ sk_B_1) @ (sk_B @ sk_B_1)) @ 
% 0.91/1.16        (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.91/1.16      inference('demod', [status(thm)], ['86', '87'])).
% 0.91/1.16  thf('89', plain,
% 0.91/1.16      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.91/1.16         ((r2_hidden @ X7 @ X8)
% 0.91/1.16          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.91/1.16      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.91/1.16  thf('90', plain, ((r2_hidden @ (sk_D @ sk_A @ sk_B_1 @ sk_B_1) @ sk_A)),
% 0.91/1.16      inference('sup-', [status(thm)], ['88', '89'])).
% 0.91/1.16  thf('91', plain, ($false), inference('demod', [status(thm)], ['57', '90'])).
% 0.91/1.16  
% 0.91/1.16  % SZS output end Refutation
% 0.91/1.16  
% 0.91/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
