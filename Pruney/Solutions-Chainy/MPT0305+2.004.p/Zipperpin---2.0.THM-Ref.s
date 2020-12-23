%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QPT6mmuA5Q

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:11 EST 2020

% Result     : Theorem 4.48s
% Output     : Refutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 249 expanded)
%              Number of leaves         :   16 (  74 expanded)
%              Depth                    :   32
%              Number of atoms          :  992 (3129 expanded)
%              Number of equality atoms :   50 ( 189 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t117_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
          & ~ ( r1_tarski @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t117_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['7'])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['18'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['17','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( k1_xboole_0 = X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ k1_xboole_0 @ X2 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( k1_xboole_0 = X2 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 = sk_A )
        | ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ k1_xboole_0 @ sk_A @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ k1_xboole_0 @ sk_A @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ( ( r1_tarski @ sk_B @ sk_C_1 )
      | ( r1_tarski @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('64',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['44','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ sk_A @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ sk_A @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QPT6mmuA5Q
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:31:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 4.48/4.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.48/4.70  % Solved by: fo/fo7.sh
% 4.48/4.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.48/4.70  % done 4373 iterations in 4.244s
% 4.48/4.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.48/4.70  % SZS output start Refutation
% 4.48/4.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.48/4.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.48/4.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.48/4.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.48/4.70  thf(sk_A_type, type, sk_A: $i).
% 4.48/4.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.48/4.70  thf(sk_B_type, type, sk_B: $i).
% 4.48/4.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.48/4.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.48/4.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.48/4.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.48/4.70  thf(t117_zfmisc_1, conjecture,
% 4.48/4.70    (![A:$i,B:$i,C:$i]:
% 4.48/4.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.48/4.70          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 4.48/4.70            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 4.48/4.70          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 4.48/4.70  thf(zf_stmt_0, negated_conjecture,
% 4.48/4.70    (~( ![A:$i,B:$i,C:$i]:
% 4.48/4.70        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.48/4.70             ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 4.48/4.70               ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 4.48/4.70             ( ~( r1_tarski @ B @ C ) ) ) ) )),
% 4.48/4.70    inference('cnf.neg', [status(esa)], [t117_zfmisc_1])).
% 4.48/4.70  thf('0', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 4.48/4.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.70  thf(d4_xboole_0, axiom,
% 4.48/4.70    (![A:$i,B:$i,C:$i]:
% 4.48/4.70     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 4.48/4.70       ( ![D:$i]:
% 4.48/4.70         ( ( r2_hidden @ D @ C ) <=>
% 4.48/4.70           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.48/4.70  thf('1', plain,
% 4.48/4.70      (![X5 : $i, X6 : $i, X9 : $i]:
% 4.48/4.70         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 4.48/4.70          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 4.48/4.70          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 4.48/4.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.48/4.70  thf('2', plain,
% 4.48/4.70      (![X5 : $i, X6 : $i, X9 : $i]:
% 4.48/4.70         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 4.48/4.70          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 4.48/4.70          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 4.48/4.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.48/4.70  thf('3', plain,
% 4.48/4.70      (![X5 : $i, X6 : $i, X9 : $i]:
% 4.48/4.70         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 4.48/4.70          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 4.48/4.70          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 4.48/4.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.48/4.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.48/4.70  thf('4', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 4.48/4.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.48/4.70  thf(d3_tarski, axiom,
% 4.48/4.70    (![A:$i,B:$i]:
% 4.48/4.70     ( ( r1_tarski @ A @ B ) <=>
% 4.48/4.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.48/4.70  thf('5', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.70         (~ (r2_hidden @ X0 @ X1)
% 4.48/4.70          | (r2_hidden @ X0 @ X2)
% 4.48/4.70          | ~ (r1_tarski @ X1 @ X2))),
% 4.48/4.70      inference('cnf', [status(esa)], [d3_tarski])).
% 4.48/4.70  thf('6', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 4.48/4.70      inference('sup-', [status(thm)], ['4', '5'])).
% 4.48/4.70  thf('7', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.70         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 4.48/4.70          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1))
% 4.48/4.70          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X2))),
% 4.48/4.70      inference('sup-', [status(thm)], ['3', '6'])).
% 4.48/4.70  thf('8', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ X0)
% 4.48/4.70          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.48/4.70      inference('condensation', [status(thm)], ['7'])).
% 4.48/4.70  thf('9', plain,
% 4.48/4.70      (![X5 : $i, X6 : $i, X9 : $i]:
% 4.48/4.70         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 4.48/4.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.48/4.70  thf('10', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ X1)
% 4.48/4.70          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['8', '9'])).
% 4.48/4.70  thf('11', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         (~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ X1)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 4.48/4.70          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.48/4.70      inference('simplify', [status(thm)], ['10'])).
% 4.48/4.70  thf('12', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 4.48/4.70      inference('sup-', [status(thm)], ['4', '5'])).
% 4.48/4.70  thf('13', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 4.48/4.70      inference('clc', [status(thm)], ['11', '12'])).
% 4.48/4.70  thf('14', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 4.48/4.70          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1))
% 4.48/4.70          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['2', '13'])).
% 4.48/4.70  thf('15', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1))
% 4.48/4.70          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0))),
% 4.48/4.70      inference('simplify', [status(thm)], ['14'])).
% 4.48/4.70  thf('16', plain,
% 4.48/4.70      (![X5 : $i, X6 : $i, X9 : $i]:
% 4.48/4.70         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 4.48/4.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.48/4.70  thf('17', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ X0)
% 4.48/4.70          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X0)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['15', '16'])).
% 4.48/4.70  thf('18', plain,
% 4.48/4.70      (![X5 : $i, X6 : $i, X9 : $i]:
% 4.48/4.70         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 4.48/4.70          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 4.48/4.70          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 4.48/4.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.48/4.70  thf('19', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.48/4.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.48/4.70      inference('eq_fact', [status(thm)], ['18'])).
% 4.48/4.70  thf('20', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.48/4.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.48/4.70      inference('eq_fact', [status(thm)], ['18'])).
% 4.48/4.70  thf('21', plain,
% 4.48/4.70      (![X5 : $i, X6 : $i, X9 : $i]:
% 4.48/4.70         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 4.48/4.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.48/4.70  thf('22', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 4.48/4.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['20', '21'])).
% 4.48/4.70  thf('23', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.48/4.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.48/4.70      inference('simplify', [status(thm)], ['22'])).
% 4.48/4.70  thf('24', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.48/4.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.48/4.70      inference('eq_fact', [status(thm)], ['18'])).
% 4.48/4.70  thf('25', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 4.48/4.70      inference('clc', [status(thm)], ['23', '24'])).
% 4.48/4.70  thf('26', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['19', '25'])).
% 4.48/4.70  thf('27', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.48/4.70      inference('simplify', [status(thm)], ['26'])).
% 4.48/4.70  thf('28', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.48/4.70      inference('simplify', [status(thm)], ['26'])).
% 4.48/4.70  thf('29', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (X0))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ X0)
% 4.48/4.70          | ((k1_xboole_0) = (X0)))),
% 4.48/4.70      inference('demod', [status(thm)], ['17', '27', '28'])).
% 4.48/4.70  thf('30', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         (~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ X0)
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 4.48/4.70          | ((k1_xboole_0) = (X0)))),
% 4.48/4.70      inference('simplify', [status(thm)], ['29'])).
% 4.48/4.70  thf('31', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i]:
% 4.48/4.70         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 4.48/4.70      inference('sup-', [status(thm)], ['4', '5'])).
% 4.48/4.70  thf('32', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (X0))
% 4.48/4.70          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 4.48/4.70      inference('clc', [status(thm)], ['30', '31'])).
% 4.48/4.70  thf('33', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ X0)
% 4.48/4.70          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))
% 4.48/4.70          | ((k1_xboole_0) = (X0)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['1', '32'])).
% 4.48/4.70  thf('34', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.48/4.70      inference('simplify', [status(thm)], ['26'])).
% 4.48/4.70  thf('35', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ X0)
% 4.48/4.70          | ((k1_xboole_0) = (X0))
% 4.48/4.70          | ((k1_xboole_0) = (X0)))),
% 4.48/4.70      inference('demod', [status(thm)], ['33', '34'])).
% 4.48/4.70  thf('36', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (X0))
% 4.48/4.70          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ X0))),
% 4.48/4.70      inference('simplify', [status(thm)], ['35'])).
% 4.48/4.70  thf('37', plain,
% 4.48/4.70      (![X1 : $i, X3 : $i]:
% 4.48/4.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.48/4.70      inference('cnf', [status(esa)], [d3_tarski])).
% 4.48/4.70  thf(l54_zfmisc_1, axiom,
% 4.48/4.70    (![A:$i,B:$i,C:$i,D:$i]:
% 4.48/4.70     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 4.48/4.70       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 4.48/4.70  thf('38', plain,
% 4.48/4.70      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 4.48/4.70         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 4.48/4.70          | ~ (r2_hidden @ X13 @ X15)
% 4.48/4.70          | ~ (r2_hidden @ X11 @ X12))),
% 4.48/4.70      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 4.48/4.70  thf('39', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.48/4.70         ((r1_tarski @ X0 @ X1)
% 4.48/4.70          | ~ (r2_hidden @ X3 @ X2)
% 4.48/4.70          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 4.48/4.70             (k2_zfmisc_1 @ X2 @ X0)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['37', '38'])).
% 4.48/4.70  thf('40', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (X0))
% 4.48/4.70          | (r2_hidden @ 
% 4.48/4.70             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ (sk_C @ X2 @ X1)) @ 
% 4.48/4.70             (k2_zfmisc_1 @ X0 @ X1))
% 4.48/4.70          | (r1_tarski @ X1 @ X2))),
% 4.48/4.70      inference('sup-', [status(thm)], ['36', '39'])).
% 4.48/4.70  thf('41', plain,
% 4.48/4.70      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70         (k2_zfmisc_1 @ sk_C_1 @ sk_A))
% 4.48/4.70        | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.48/4.70           (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 4.48/4.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.70  thf('42', plain,
% 4.48/4.70      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.48/4.70         (k2_zfmisc_1 @ sk_A @ sk_C_1)))
% 4.48/4.70         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.48/4.70               (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 4.48/4.70      inference('split', [status(esa)], ['41'])).
% 4.48/4.70  thf('43', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.70         (~ (r2_hidden @ X0 @ X1)
% 4.48/4.70          | (r2_hidden @ X0 @ X2)
% 4.48/4.70          | ~ (r1_tarski @ X1 @ X2))),
% 4.48/4.70      inference('cnf', [status(esa)], [d3_tarski])).
% 4.48/4.70  thf('44', plain,
% 4.48/4.70      ((![X0 : $i]:
% 4.48/4.70          ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 4.48/4.70           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 4.48/4.70         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.48/4.70               (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 4.48/4.70      inference('sup-', [status(thm)], ['42', '43'])).
% 4.48/4.70  thf('45', plain,
% 4.48/4.70      (![X1 : $i, X3 : $i]:
% 4.48/4.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.48/4.70      inference('cnf', [status(esa)], [d3_tarski])).
% 4.48/4.70  thf('46', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (X0))
% 4.48/4.70          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ X0))),
% 4.48/4.70      inference('simplify', [status(thm)], ['35'])).
% 4.48/4.70  thf('47', plain,
% 4.48/4.70      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 4.48/4.70         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 4.48/4.70          | ~ (r2_hidden @ X13 @ X15)
% 4.48/4.70          | ~ (r2_hidden @ X11 @ X12))),
% 4.48/4.70      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 4.48/4.70  thf('48', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.70         (((k1_xboole_0) = (X0))
% 4.48/4.70          | ~ (r2_hidden @ X2 @ X1)
% 4.48/4.70          | (r2_hidden @ (k4_tarski @ X2 @ (sk_D @ k1_xboole_0 @ X0 @ X0)) @ 
% 4.48/4.70             (k2_zfmisc_1 @ X1 @ X0)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['46', '47'])).
% 4.48/4.70  thf('49', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.70         ((r1_tarski @ X0 @ X1)
% 4.48/4.70          | (r2_hidden @ 
% 4.48/4.70             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ k1_xboole_0 @ X2 @ X2)) @ 
% 4.48/4.70             (k2_zfmisc_1 @ X0 @ X2))
% 4.48/4.70          | ((k1_xboole_0) = (X2)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['45', '48'])).
% 4.48/4.70  thf('50', plain,
% 4.48/4.70      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70         (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 4.48/4.70         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 4.48/4.70      inference('split', [status(esa)], ['41'])).
% 4.48/4.70  thf('51', plain,
% 4.48/4.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.48/4.70         (~ (r2_hidden @ X0 @ X1)
% 4.48/4.70          | (r2_hidden @ X0 @ X2)
% 4.48/4.70          | ~ (r1_tarski @ X1 @ X2))),
% 4.48/4.70      inference('cnf', [status(esa)], [d3_tarski])).
% 4.48/4.70  thf('52', plain,
% 4.48/4.70      ((![X0 : $i]:
% 4.48/4.70          ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))
% 4.48/4.70           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.48/4.70         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 4.48/4.70      inference('sup-', [status(thm)], ['50', '51'])).
% 4.48/4.70  thf('53', plain,
% 4.48/4.70      ((![X0 : $i]:
% 4.48/4.70          (((k1_xboole_0) = (sk_A))
% 4.48/4.70           | (r1_tarski @ sk_B @ X0)
% 4.48/4.70           | (r2_hidden @ 
% 4.48/4.70              (k4_tarski @ (sk_C @ X0 @ sk_B) @ 
% 4.48/4.70               (sk_D @ k1_xboole_0 @ sk_A @ sk_A)) @ 
% 4.48/4.70              (k2_zfmisc_1 @ sk_C_1 @ sk_A))))
% 4.48/4.70         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 4.48/4.70      inference('sup-', [status(thm)], ['49', '52'])).
% 4.48/4.70  thf('54', plain, (((sk_A) != (k1_xboole_0))),
% 4.48/4.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.70  thf('55', plain,
% 4.48/4.70      ((![X0 : $i]:
% 4.48/4.70          ((r1_tarski @ sk_B @ X0)
% 4.48/4.70           | (r2_hidden @ 
% 4.48/4.70              (k4_tarski @ (sk_C @ X0 @ sk_B) @ 
% 4.48/4.70               (sk_D @ k1_xboole_0 @ sk_A @ sk_A)) @ 
% 4.48/4.70              (k2_zfmisc_1 @ sk_C_1 @ sk_A))))
% 4.48/4.70         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 4.48/4.70      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 4.48/4.70  thf('56', plain,
% 4.48/4.70      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 4.48/4.70         ((r2_hidden @ X11 @ X12)
% 4.48/4.70          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 4.48/4.70      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 4.48/4.70  thf('57', plain,
% 4.48/4.70      ((![X0 : $i]:
% 4.48/4.70          ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1)))
% 4.48/4.70         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 4.48/4.70      inference('sup-', [status(thm)], ['55', '56'])).
% 4.48/4.70  thf('58', plain,
% 4.48/4.70      (![X1 : $i, X3 : $i]:
% 4.48/4.70         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.48/4.70      inference('cnf', [status(esa)], [d3_tarski])).
% 4.48/4.70  thf('59', plain,
% 4.48/4.70      ((((r1_tarski @ sk_B @ sk_C_1) | (r1_tarski @ sk_B @ sk_C_1)))
% 4.48/4.70         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 4.48/4.70      inference('sup-', [status(thm)], ['57', '58'])).
% 4.48/4.70  thf('60', plain,
% 4.48/4.70      (((r1_tarski @ sk_B @ sk_C_1))
% 4.48/4.70         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 4.48/4.70      inference('simplify', [status(thm)], ['59'])).
% 4.48/4.70  thf('61', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 4.48/4.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.70  thf('62', plain,
% 4.48/4.70      (~
% 4.48/4.70       ((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70         (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['60', '61'])).
% 4.48/4.70  thf('63', plain,
% 4.48/4.70      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.48/4.70         (k2_zfmisc_1 @ sk_A @ sk_C_1))) | 
% 4.48/4.70       ((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 4.48/4.70         (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 4.48/4.70      inference('split', [status(esa)], ['41'])).
% 4.48/4.70  thf('64', plain,
% 4.48/4.70      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 4.48/4.70         (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 4.48/4.70      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 4.48/4.70  thf('65', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 4.48/4.70          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.48/4.70      inference('simpl_trail', [status(thm)], ['44', '64'])).
% 4.48/4.70  thf('66', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         ((r1_tarski @ sk_B @ X0)
% 4.48/4.70          | ((k1_xboole_0) = (sk_A))
% 4.48/4.70          | (r2_hidden @ 
% 4.48/4.70             (k4_tarski @ (sk_D @ k1_xboole_0 @ sk_A @ sk_A) @ 
% 4.48/4.70              (sk_C @ X0 @ sk_B)) @ 
% 4.48/4.70             (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 4.48/4.70      inference('sup-', [status(thm)], ['40', '65'])).
% 4.48/4.70  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 4.48/4.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.48/4.70  thf('68', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         ((r1_tarski @ sk_B @ X0)
% 4.48/4.70          | (r2_hidden @ 
% 4.48/4.70             (k4_tarski @ (sk_D @ k1_xboole_0 @ sk_A @ sk_A) @ 
% 4.48/4.70              (sk_C @ X0 @ sk_B)) @ 
% 4.48/4.70             (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 4.48/4.70      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 4.48/4.70  thf('69', plain,
% 4.48/4.70      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 4.48/4.70         ((r2_hidden @ X13 @ X14)
% 4.48/4.70          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 4.48/4.70      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 4.48/4.70  thf('70', plain,
% 4.48/4.70      (![X0 : $i]:
% 4.48/4.70         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1))),
% 4.48/4.70      inference('sup-', [status(thm)], ['68', '69'])).
% 4.48/4.70  thf('71', plain,
% 4.48/4.70      (![X1 : $i, X3 : $i]:
% 4.48/4.70         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.48/4.70      inference('cnf', [status(esa)], [d3_tarski])).
% 4.48/4.70  thf('72', plain,
% 4.48/4.70      (((r1_tarski @ sk_B @ sk_C_1) | (r1_tarski @ sk_B @ sk_C_1))),
% 4.48/4.70      inference('sup-', [status(thm)], ['70', '71'])).
% 4.48/4.70  thf('73', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 4.48/4.70      inference('simplify', [status(thm)], ['72'])).
% 4.48/4.70  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 4.48/4.70  
% 4.48/4.70  % SZS output end Refutation
% 4.48/4.70  
% 4.48/4.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
