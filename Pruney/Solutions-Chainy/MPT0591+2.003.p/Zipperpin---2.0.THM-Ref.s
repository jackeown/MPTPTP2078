%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.au9MWzlnuj

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:35 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 206 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   26
%              Number of atoms          :  907 (2053 expanded)
%              Number of equality atoms :   70 ( 146 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18
        = ( k1_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X18 @ X15 ) @ ( sk_D @ X18 @ X15 ) ) @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(condensation,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(condensation,[status(thm)],['6'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('12',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X15: $i,X18: $i,X19: $i] :
      ( ( X18
        = ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X18 @ X15 ) @ X19 ) @ X15 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X18 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('15',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(condensation,[status(thm)],['6'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X12 ) )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X22 )
      | ( r2_hidden @ X21 @ X23 )
      | ( X23
       != ( k2_relat_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k2_relat_1 @ X22 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X22 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X24 @ X22 ) @ X24 ) @ X22 )
      | ( X23
       != ( k2_relat_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('34',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X24 @ X22 ) @ X24 ) @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k2_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['31','40'])).

thf(t195_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
                = A )
              & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
                = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t195_relat_1])).

thf('42',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','18'])).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X12 ) )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_1 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X1 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['56','64'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('67',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('72',plain,(
    ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['43','72'])).

thf('74',plain,
    ( ( sk_B != sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','73'])).

thf('75',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.au9MWzlnuj
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.72/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.93  % Solved by: fo/fo7.sh
% 0.72/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.93  % done 316 iterations in 0.470s
% 0.72/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.93  % SZS output start Refutation
% 0.72/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.72/0.93  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.72/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.72/0.93  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.72/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.72/0.93  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 0.72/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.72/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.72/0.93  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.72/0.93  thf(d4_relat_1, axiom,
% 0.72/0.93    (![A:$i,B:$i]:
% 0.72/0.93     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.72/0.93       ( ![C:$i]:
% 0.72/0.93         ( ( r2_hidden @ C @ B ) <=>
% 0.72/0.93           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.72/0.93  thf('0', plain,
% 0.72/0.93      (![X15 : $i, X18 : $i]:
% 0.72/0.93         (((X18) = (k1_relat_1 @ X15))
% 0.72/0.93          | (r2_hidden @ 
% 0.72/0.93             (k4_tarski @ (sk_C_1 @ X18 @ X15) @ (sk_D @ X18 @ X15)) @ X15)
% 0.72/0.93          | (r2_hidden @ (sk_C_1 @ X18 @ X15) @ X18))),
% 0.72/0.93      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.72/0.93  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.72/0.93  thf('1', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.72/0.93      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.72/0.93  thf(d3_tarski, axiom,
% 0.72/0.93    (![A:$i,B:$i]:
% 0.72/0.93     ( ( r1_tarski @ A @ B ) <=>
% 0.72/0.93       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.72/0.93  thf('2', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         (~ (r2_hidden @ X0 @ X1)
% 0.72/0.93          | (r2_hidden @ X0 @ X2)
% 0.72/0.93          | ~ (r1_tarski @ X1 @ X2))),
% 0.72/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.93  thf('3', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.72/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.72/0.93  thf('4', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.72/0.93          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ 
% 0.72/0.93             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 0.72/0.93              (sk_D @ X0 @ k1_xboole_0)) @ 
% 0.72/0.93             X1))),
% 0.72/0.93      inference('sup-', [status(thm)], ['0', '3'])).
% 0.72/0.93  thf(l54_zfmisc_1, axiom,
% 0.72/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.93     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.72/0.93       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.72/0.93  thf('5', plain,
% 0.72/0.93      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.72/0.93         ((r2_hidden @ X8 @ X9)
% 0.72/0.93          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.72/0.93      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.72/0.93  thf('6', plain,
% 0.72/0.93      (![X1 : $i, X2 : $i]:
% 0.72/0.93         (((X2) = (k1_relat_1 @ k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 0.72/0.93          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X1))),
% 0.72/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.72/0.93  thf('7', plain,
% 0.72/0.93      (![X0 : $i]:
% 0.72/0.93         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.72/0.93      inference('condensation', [status(thm)], ['6'])).
% 0.72/0.93  thf('8', plain,
% 0.72/0.93      (![X0 : $i]:
% 0.72/0.93         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.72/0.93      inference('condensation', [status(thm)], ['6'])).
% 0.72/0.93  thf('9', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.72/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.72/0.93  thf('10', plain,
% 0.72/0.93      (![X0 : $i]:
% 0.72/0.93         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 0.72/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.72/0.93  thf('11', plain,
% 0.72/0.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.72/0.93         (~ (r2_hidden @ X17 @ X16)
% 0.72/0.93          | (r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 0.72/0.93          | ((X16) != (k1_relat_1 @ X15)))),
% 0.72/0.93      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.72/0.93  thf('12', plain,
% 0.72/0.93      (![X15 : $i, X17 : $i]:
% 0.72/0.93         ((r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 0.72/0.93          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X15)))),
% 0.72/0.93      inference('simplify', [status(thm)], ['11'])).
% 0.72/0.93  thf('13', plain,
% 0.72/0.93      (![X0 : $i]:
% 0.72/0.93         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ 
% 0.72/0.93             (k4_tarski @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.72/0.93              (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0)) @ 
% 0.72/0.93             X0))),
% 0.72/0.93      inference('sup-', [status(thm)], ['10', '12'])).
% 0.72/0.93  thf('14', plain,
% 0.72/0.93      (![X15 : $i, X18 : $i, X19 : $i]:
% 0.72/0.93         (((X18) = (k1_relat_1 @ X15))
% 0.72/0.93          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X18 @ X15) @ X19) @ X15)
% 0.72/0.93          | ~ (r2_hidden @ (sk_C_1 @ X18 @ X15) @ X18))),
% 0.72/0.93      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.72/0.93  thf('15', plain,
% 0.72/0.93      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.72/0.93        | ~ (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 0.72/0.93        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.72/0.93      inference('sup-', [status(thm)], ['13', '14'])).
% 0.72/0.93  thf('16', plain,
% 0.72/0.93      ((~ (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 0.72/0.93        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.72/0.93      inference('simplify', [status(thm)], ['15'])).
% 0.72/0.93  thf('17', plain,
% 0.72/0.93      (![X0 : $i]:
% 0.72/0.93         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.72/0.93      inference('condensation', [status(thm)], ['6'])).
% 0.72/0.93  thf('18', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.72/0.93      inference('clc', [status(thm)], ['16', '17'])).
% 0.72/0.93  thf('19', plain,
% 0.72/0.93      (![X0 : $i]:
% 0.72/0.93         (((X0) = (k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.72/0.93      inference('demod', [status(thm)], ['7', '18'])).
% 0.72/0.93  thf('20', plain,
% 0.72/0.93      (![X1 : $i, X3 : $i]:
% 0.72/0.93         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.72/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.93  thf('21', plain,
% 0.72/0.93      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.72/0.93         ((r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X12))
% 0.72/0.93          | ~ (r2_hidden @ X10 @ X12)
% 0.72/0.93          | ~ (r2_hidden @ X8 @ X9))),
% 0.72/0.93      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.72/0.93  thf('22', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.93         ((r1_tarski @ X0 @ X1)
% 0.72/0.93          | ~ (r2_hidden @ X3 @ X2)
% 0.72/0.93          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.72/0.93             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.72/0.93      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.93  thf('23', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         (((X0) = (k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ 
% 0.72/0.93             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 0.72/0.93             (k2_zfmisc_1 @ X0 @ X1))
% 0.72/0.93          | (r1_tarski @ X1 @ X2))),
% 0.72/0.93      inference('sup-', [status(thm)], ['19', '22'])).
% 0.72/0.93  thf(d5_relat_1, axiom,
% 0.72/0.93    (![A:$i,B:$i]:
% 0.72/0.93     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.72/0.93       ( ![C:$i]:
% 0.72/0.93         ( ( r2_hidden @ C @ B ) <=>
% 0.72/0.93           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.72/0.93  thf('24', plain,
% 0.72/0.93      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.72/0.93         (~ (r2_hidden @ (k4_tarski @ X20 @ X21) @ X22)
% 0.72/0.93          | (r2_hidden @ X21 @ X23)
% 0.72/0.93          | ((X23) != (k2_relat_1 @ X22)))),
% 0.72/0.93      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.72/0.93  thf('25', plain,
% 0.72/0.93      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.72/0.93         ((r2_hidden @ X21 @ (k2_relat_1 @ X22))
% 0.72/0.93          | ~ (r2_hidden @ (k4_tarski @ X20 @ X21) @ X22))),
% 0.72/0.93      inference('simplify', [status(thm)], ['24'])).
% 0.72/0.93  thf('26', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         ((r1_tarski @ X0 @ X2)
% 0.72/0.93          | ((X1) = (k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ (sk_C @ X2 @ X0) @ 
% 0.72/0.93             (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.72/0.93      inference('sup-', [status(thm)], ['23', '25'])).
% 0.72/0.93  thf('27', plain,
% 0.72/0.93      (![X1 : $i, X3 : $i]:
% 0.72/0.93         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.72/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.93  thf('28', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         (((X1) = (k1_xboole_0))
% 0.72/0.93          | (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.72/0.93          | (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.72/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.72/0.93  thf('29', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.72/0.93          | ((X1) = (k1_xboole_0)))),
% 0.72/0.93      inference('simplify', [status(thm)], ['28'])).
% 0.72/0.93  thf(d10_xboole_0, axiom,
% 0.72/0.93    (![A:$i,B:$i]:
% 0.72/0.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.72/0.93  thf('30', plain,
% 0.72/0.93      (![X4 : $i, X6 : $i]:
% 0.72/0.93         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.72/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.72/0.93  thf('31', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         (((X1) = (k1_xboole_0))
% 0.72/0.93          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 0.72/0.93          | ((k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) = (X0)))),
% 0.72/0.93      inference('sup-', [status(thm)], ['29', '30'])).
% 0.72/0.93  thf('32', plain,
% 0.72/0.93      (![X1 : $i, X3 : $i]:
% 0.72/0.93         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.72/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.93  thf('33', plain,
% 0.72/0.93      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.72/0.93         (~ (r2_hidden @ X24 @ X23)
% 0.72/0.93          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X24 @ X22) @ X24) @ X22)
% 0.72/0.93          | ((X23) != (k2_relat_1 @ X22)))),
% 0.72/0.93      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.72/0.93  thf('34', plain,
% 0.72/0.93      (![X22 : $i, X24 : $i]:
% 0.72/0.93         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X24 @ X22) @ X24) @ X22)
% 0.72/0.93          | ~ (r2_hidden @ X24 @ (k2_relat_1 @ X22)))),
% 0.72/0.93      inference('simplify', [status(thm)], ['33'])).
% 0.72/0.93  thf('35', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.72/0.93          | (r2_hidden @ 
% 0.72/0.93             (k4_tarski @ (sk_D_3 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.72/0.93              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 0.72/0.93             X0))),
% 0.72/0.93      inference('sup-', [status(thm)], ['32', '34'])).
% 0.72/0.93  thf('36', plain,
% 0.72/0.93      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.72/0.93         ((r2_hidden @ X10 @ X11)
% 0.72/0.93          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.72/0.93      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.72/0.93  thf('37', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         ((r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 0.72/0.93          | (r2_hidden @ 
% 0.72/0.93             (sk_C @ X2 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.72/0.93      inference('sup-', [status(thm)], ['35', '36'])).
% 0.72/0.93  thf('38', plain,
% 0.72/0.93      (![X1 : $i, X3 : $i]:
% 0.72/0.93         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.72/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.93  thf('39', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 0.72/0.93          | (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 0.72/0.93      inference('sup-', [status(thm)], ['37', '38'])).
% 0.72/0.93  thf('40', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)),
% 0.72/0.93      inference('simplify', [status(thm)], ['39'])).
% 0.72/0.93  thf('41', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         (((X1) = (k1_xboole_0))
% 0.72/0.93          | ((k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) = (X0)))),
% 0.72/0.93      inference('demod', [status(thm)], ['31', '40'])).
% 0.72/0.93  thf(t195_relat_1, conjecture,
% 0.72/0.93    (![A:$i,B:$i]:
% 0.72/0.93     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.72/0.93          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.72/0.93               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.72/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.93    (~( ![A:$i,B:$i]:
% 0.72/0.93        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.72/0.93             ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.72/0.93                  ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ) )),
% 0.72/0.93    inference('cnf.neg', [status(esa)], [t195_relat_1])).
% 0.72/0.93  thf('42', plain,
% 0.72/0.93      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A))
% 0.72/0.93        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B)))),
% 0.72/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.93  thf('43', plain,
% 0.72/0.93      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B)))
% 0.72/0.93         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 0.72/0.93      inference('split', [status(esa)], ['42'])).
% 0.72/0.93  thf('44', plain,
% 0.72/0.93      (![X1 : $i, X3 : $i]:
% 0.72/0.93         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.72/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.93  thf('45', plain,
% 0.72/0.93      (![X0 : $i]:
% 0.72/0.93         (((X0) = (k1_xboole_0))
% 0.72/0.93          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.72/0.93      inference('demod', [status(thm)], ['7', '18'])).
% 0.72/0.93  thf('46', plain,
% 0.72/0.93      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.72/0.93         ((r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X12))
% 0.72/0.93          | ~ (r2_hidden @ X10 @ X12)
% 0.72/0.93          | ~ (r2_hidden @ X8 @ X9))),
% 0.72/0.93      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.72/0.93  thf('47', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         (((X0) = (k1_xboole_0))
% 0.72/0.93          | ~ (r2_hidden @ X2 @ X1)
% 0.72/0.93          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 0.72/0.93             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.72/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.72/0.93  thf('48', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         ((r1_tarski @ X0 @ X1)
% 0.72/0.93          | (r2_hidden @ 
% 0.72/0.93             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_1 @ X2 @ k1_xboole_0)) @ 
% 0.72/0.93             (k2_zfmisc_1 @ X0 @ X2))
% 0.72/0.93          | ((X2) = (k1_xboole_0)))),
% 0.72/0.93      inference('sup-', [status(thm)], ['44', '47'])).
% 0.72/0.93  thf('49', plain,
% 0.72/0.93      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.72/0.93         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 0.72/0.93          | (r2_hidden @ X13 @ X16)
% 0.72/0.93          | ((X16) != (k1_relat_1 @ X15)))),
% 0.72/0.93      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.72/0.93  thf('50', plain,
% 0.72/0.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.72/0.93         ((r2_hidden @ X13 @ (k1_relat_1 @ X15))
% 0.72/0.93          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.72/0.93      inference('simplify', [status(thm)], ['49'])).
% 0.72/0.93  thf('51', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         (((X0) = (k1_xboole_0))
% 0.72/0.93          | (r1_tarski @ X1 @ X2)
% 0.72/0.93          | (r2_hidden @ (sk_C @ X2 @ X1) @ 
% 0.72/0.93             (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.72/0.93      inference('sup-', [status(thm)], ['48', '50'])).
% 0.72/0.93  thf('52', plain,
% 0.72/0.93      (![X1 : $i, X3 : $i]:
% 0.72/0.93         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.72/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.93  thf('53', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.72/0.93          | ((X0) = (k1_xboole_0))
% 0.72/0.93          | (r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.72/0.93      inference('sup-', [status(thm)], ['51', '52'])).
% 0.72/0.93  thf('54', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         (((X0) = (k1_xboole_0))
% 0.72/0.93          | (r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.72/0.93      inference('simplify', [status(thm)], ['53'])).
% 0.72/0.93  thf('55', plain,
% 0.72/0.93      (![X4 : $i, X6 : $i]:
% 0.72/0.93         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.72/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.72/0.93  thf('56', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         (((X0) = (k1_xboole_0))
% 0.72/0.93          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X1)
% 0.72/0.93          | ((k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) = (X1)))),
% 0.72/0.93      inference('sup-', [status(thm)], ['54', '55'])).
% 0.72/0.93  thf('57', plain,
% 0.72/0.93      (![X1 : $i, X3 : $i]:
% 0.72/0.93         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.72/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.93  thf('58', plain,
% 0.72/0.93      (![X15 : $i, X17 : $i]:
% 0.72/0.93         ((r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 0.72/0.93          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X15)))),
% 0.72/0.93      inference('simplify', [status(thm)], ['11'])).
% 0.72/0.93  thf('59', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.72/0.93          | (r2_hidden @ 
% 0.72/0.93             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.72/0.93              (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.72/0.93             X0))),
% 0.72/0.93      inference('sup-', [status(thm)], ['57', '58'])).
% 0.72/0.93  thf('60', plain,
% 0.72/0.93      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.72/0.93         ((r2_hidden @ X8 @ X9)
% 0.72/0.93          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.72/0.93      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.72/0.93  thf('61', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.93         ((r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 0.72/0.93          | (r2_hidden @ 
% 0.72/0.93             (sk_C @ X2 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.72/0.93      inference('sup-', [status(thm)], ['59', '60'])).
% 0.72/0.93  thf('62', plain,
% 0.72/0.93      (![X1 : $i, X3 : $i]:
% 0.72/0.93         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.72/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.93  thf('63', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         ((r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)
% 0.72/0.93          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 0.72/0.93      inference('sup-', [status(thm)], ['61', '62'])).
% 0.72/0.93  thf('64', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 0.72/0.93      inference('simplify', [status(thm)], ['63'])).
% 0.72/0.93  thf('65', plain,
% 0.72/0.93      (![X0 : $i, X1 : $i]:
% 0.72/0.93         (((X0) = (k1_xboole_0))
% 0.72/0.93          | ((k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) = (X1)))),
% 0.72/0.93      inference('demod', [status(thm)], ['56', '64'])).
% 0.72/0.93  thf('66', plain,
% 0.72/0.93      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A)))
% 0.72/0.93         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))))),
% 0.72/0.93      inference('split', [status(esa)], ['42'])).
% 0.72/0.93  thf('67', plain,
% 0.72/0.93      (((((sk_A) != (sk_A)) | ((sk_B) = (k1_xboole_0))))
% 0.72/0.93         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))))),
% 0.72/0.93      inference('sup-', [status(thm)], ['65', '66'])).
% 0.72/0.93  thf('68', plain,
% 0.72/0.93      ((((sk_B) = (k1_xboole_0)))
% 0.72/0.93         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))))),
% 0.72/0.93      inference('simplify', [status(thm)], ['67'])).
% 0.72/0.93  thf('69', plain, (((sk_B) != (k1_xboole_0))),
% 0.72/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.93  thf('70', plain, ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A)))),
% 0.72/0.93      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.72/0.93  thf('71', plain,
% 0.72/0.93      (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))) | 
% 0.72/0.93       ~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A)))),
% 0.72/0.93      inference('split', [status(esa)], ['42'])).
% 0.72/0.93  thf('72', plain, (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B)))),
% 0.72/0.93      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.72/0.93  thf('73', plain, (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B))),
% 0.72/0.93      inference('simpl_trail', [status(thm)], ['43', '72'])).
% 0.72/0.93  thf('74', plain, ((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.72/0.93      inference('sup-', [status(thm)], ['41', '73'])).
% 0.72/0.93  thf('75', plain, (((sk_A) = (k1_xboole_0))),
% 0.72/0.93      inference('simplify', [status(thm)], ['74'])).
% 0.72/0.93  thf('76', plain, (((sk_A) != (k1_xboole_0))),
% 0.72/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.93  thf('77', plain, ($false),
% 0.72/0.93      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.72/0.93  
% 0.72/0.93  % SZS output end Refutation
% 0.72/0.93  
% 0.77/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
