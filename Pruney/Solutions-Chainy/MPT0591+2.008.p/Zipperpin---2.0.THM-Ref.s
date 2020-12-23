%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R16eaymTgw

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:36 EST 2020

% Result     : Theorem 3.75s
% Output     : Refutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 207 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   27
%              Number of atoms          :  884 (2348 expanded)
%              Number of equality atoms :   95 ( 237 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X10 ) @ ( sk_D @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ k1_xboole_0 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['5'])).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['5'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['5'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k1_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X1
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['8','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D_1 @ X12 @ X10 ) ) @ X10 )
      | ( X11
       != ( k1_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('20',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D_1 @ X12 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ ( sk_D_1 @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X10 ) @ X14 ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('23',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['5'])).

thf('26',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','26'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X20 @ X17 ) @ ( sk_C_1 @ X20 @ X17 ) ) @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X17: $i,X20: $i,X21: $i] :
      ( ( X20
        = ( k2_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_C_1 @ X20 @ X17 ) ) @ X17 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

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

thf('40',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13
        = ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X10 ) @ ( sk_D @ X13 @ X10 ) ) @ X10 )
      | ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('47',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ ( sk_C @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X13 @ X10 ) @ X14 ) @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X13 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['44'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('56',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_B )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('61',plain,(
    ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['59','60'])).

thf('62',plain,(
    ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['41','61'])).

thf('63',plain,
    ( ( sk_B != sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','62'])).

thf('64',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R16eaymTgw
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.75/3.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.75/3.97  % Solved by: fo/fo7.sh
% 3.75/3.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.75/3.97  % done 905 iterations in 3.512s
% 3.75/3.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.75/3.97  % SZS output start Refutation
% 3.75/3.97  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.75/3.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.75/3.97  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 3.75/3.97  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 3.75/3.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.75/3.97  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.75/3.97  thf(sk_B_type, type, sk_B: $i).
% 3.75/3.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.75/3.97  thf(sk_A_type, type, sk_A: $i).
% 3.75/3.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.75/3.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.75/3.97  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.75/3.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.75/3.97  thf(d4_relat_1, axiom,
% 3.75/3.97    (![A:$i,B:$i]:
% 3.75/3.97     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.75/3.97       ( ![C:$i]:
% 3.75/3.97         ( ( r2_hidden @ C @ B ) <=>
% 3.75/3.97           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.75/3.97  thf('0', plain,
% 3.75/3.97      (![X10 : $i, X13 : $i]:
% 3.75/3.97         (((X13) = (k1_relat_1 @ X10))
% 3.75/3.97          | (r2_hidden @ 
% 3.75/3.97             (k4_tarski @ (sk_C @ X13 @ X10) @ (sk_D @ X13 @ X10)) @ X10)
% 3.75/3.97          | (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 3.75/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.75/3.97  thf(t113_zfmisc_1, axiom,
% 3.75/3.97    (![A:$i,B:$i]:
% 3.75/3.97     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.75/3.97       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.75/3.97  thf('1', plain,
% 3.75/3.97      (![X6 : $i, X7 : $i]:
% 3.75/3.97         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 3.75/3.97      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.75/3.97  thf('2', plain,
% 3.75/3.97      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.75/3.97      inference('simplify', [status(thm)], ['1'])).
% 3.75/3.97  thf(l54_zfmisc_1, axiom,
% 3.75/3.97    (![A:$i,B:$i,C:$i,D:$i]:
% 3.75/3.97     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 3.75/3.97       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 3.75/3.97  thf('3', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.75/3.97         ((r2_hidden @ X0 @ X1)
% 3.75/3.97          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 3.75/3.97      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.75/3.97  thf('4', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.75/3.97         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ k1_xboole_0)
% 3.75/3.97          | (r2_hidden @ X2 @ X0))),
% 3.75/3.97      inference('sup-', [status(thm)], ['2', '3'])).
% 3.75/3.97  thf('5', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 3.75/3.97          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X1))),
% 3.75/3.97      inference('sup-', [status(thm)], ['0', '4'])).
% 3.75/3.97  thf('6', plain,
% 3.75/3.97      (![X0 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 3.75/3.97          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.75/3.97      inference('condensation', [status(thm)], ['5'])).
% 3.75/3.97  thf('7', plain,
% 3.75/3.97      (![X6 : $i, X7 : $i]:
% 3.75/3.97         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.75/3.97      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.75/3.97  thf('8', plain,
% 3.75/3.97      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 3.75/3.97      inference('simplify', [status(thm)], ['7'])).
% 3.75/3.97  thf('9', plain,
% 3.75/3.97      (![X0 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 3.75/3.97          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.75/3.97      inference('condensation', [status(thm)], ['5'])).
% 3.75/3.97  thf('10', plain,
% 3.75/3.97      (![X0 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 3.75/3.97          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.75/3.97      inference('condensation', [status(thm)], ['5'])).
% 3.75/3.97  thf('11', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 3.75/3.97         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 3.75/3.97          | ~ (r2_hidden @ X2 @ X4)
% 3.75/3.97          | ~ (r2_hidden @ X0 @ X1))),
% 3.75/3.97      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.75/3.97  thf('12', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.75/3.97         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97          | ~ (r2_hidden @ X2 @ X1)
% 3.75/3.97          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ X0 @ k1_xboole_0)) @ 
% 3.75/3.97             (k2_zfmisc_1 @ X1 @ X0)))),
% 3.75/3.97      inference('sup-', [status(thm)], ['10', '11'])).
% 3.75/3.97  thf('13', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97          | (r2_hidden @ 
% 3.75/3.97             (k4_tarski @ (sk_C @ X0 @ k1_xboole_0) @ (sk_C @ X1 @ k1_xboole_0)) @ 
% 3.75/3.97             (k2_zfmisc_1 @ X0 @ X1))
% 3.75/3.97          | ((X1) = (k1_relat_1 @ k1_xboole_0)))),
% 3.75/3.97      inference('sup-', [status(thm)], ['9', '12'])).
% 3.75/3.97  thf('14', plain,
% 3.75/3.97      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.75/3.97         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 3.75/3.97          | (r2_hidden @ X8 @ X11)
% 3.75/3.97          | ((X11) != (k1_relat_1 @ X10)))),
% 3.75/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.75/3.97  thf('15', plain,
% 3.75/3.97      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.75/3.97         ((r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 3.75/3.97          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 3.75/3.97      inference('simplify', [status(thm)], ['14'])).
% 3.75/3.97  thf('16', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97          | ((X1) = (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97          | (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ 
% 3.75/3.97             (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.75/3.97      inference('sup-', [status(thm)], ['13', '15'])).
% 3.75/3.97  thf('17', plain,
% 3.75/3.97      (![X0 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ 
% 3.75/3.97           (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97          | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.75/3.97      inference('sup+', [status(thm)], ['8', '16'])).
% 3.75/3.97  thf('18', plain,
% 3.75/3.97      (((r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ 
% 3.75/3.97         (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.75/3.97      inference('condensation', [status(thm)], ['17'])).
% 3.75/3.97  thf('19', plain,
% 3.75/3.97      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.75/3.97         (~ (r2_hidden @ X12 @ X11)
% 3.75/3.97          | (r2_hidden @ (k4_tarski @ X12 @ (sk_D_1 @ X12 @ X10)) @ X10)
% 3.75/3.97          | ((X11) != (k1_relat_1 @ X10)))),
% 3.75/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.75/3.97  thf('20', plain,
% 3.75/3.97      (![X10 : $i, X12 : $i]:
% 3.75/3.97         ((r2_hidden @ (k4_tarski @ X12 @ (sk_D_1 @ X12 @ X10)) @ X10)
% 3.75/3.97          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X10)))),
% 3.75/3.97      inference('simplify', [status(thm)], ['19'])).
% 3.75/3.97  thf('21', plain,
% 3.75/3.97      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97        | (r2_hidden @ 
% 3.75/3.97           (k4_tarski @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ 
% 3.75/3.97            (sk_D_1 @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 3.75/3.97           k1_xboole_0))),
% 3.75/3.97      inference('sup-', [status(thm)], ['18', '20'])).
% 3.75/3.97  thf('22', plain,
% 3.75/3.97      (![X10 : $i, X13 : $i, X14 : $i]:
% 3.75/3.97         (((X13) = (k1_relat_1 @ X10))
% 3.75/3.97          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X13 @ X10) @ X14) @ X10)
% 3.75/3.97          | ~ (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 3.75/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.75/3.97  thf('23', plain,
% 3.75/3.97      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97        | ~ (r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 3.75/3.97        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.75/3.97      inference('sup-', [status(thm)], ['21', '22'])).
% 3.75/3.97  thf('24', plain,
% 3.75/3.97      ((~ (r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 3.75/3.97        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.75/3.97      inference('simplify', [status(thm)], ['23'])).
% 3.75/3.97  thf('25', plain,
% 3.75/3.97      (![X0 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 3.75/3.97          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.75/3.97      inference('condensation', [status(thm)], ['5'])).
% 3.75/3.97  thf('26', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.75/3.97      inference('clc', [status(thm)], ['24', '25'])).
% 3.75/3.97  thf('27', plain,
% 3.75/3.97      (![X0 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 3.75/3.97      inference('demod', [status(thm)], ['6', '26'])).
% 3.75/3.97  thf(d5_relat_1, axiom,
% 3.75/3.97    (![A:$i,B:$i]:
% 3.75/3.97     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.75/3.97       ( ![C:$i]:
% 3.75/3.97         ( ( r2_hidden @ C @ B ) <=>
% 3.75/3.97           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 3.75/3.97  thf('28', plain,
% 3.75/3.97      (![X17 : $i, X20 : $i]:
% 3.75/3.97         (((X20) = (k2_relat_1 @ X17))
% 3.75/3.97          | (r2_hidden @ 
% 3.75/3.97             (k4_tarski @ (sk_D_2 @ X20 @ X17) @ (sk_C_1 @ X20 @ X17)) @ X17)
% 3.75/3.97          | (r2_hidden @ (sk_C_1 @ X20 @ X17) @ X20))),
% 3.75/3.97      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.75/3.97  thf('29', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.75/3.97         ((r2_hidden @ X2 @ X3)
% 3.75/3.97          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 3.75/3.97      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.75/3.97  thf('30', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C_1 @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 3.75/3.97          | ((X2) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.75/3.97          | (r2_hidden @ (sk_C_1 @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 3.75/3.97      inference('sup-', [status(thm)], ['28', '29'])).
% 3.75/3.97  thf('31', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 3.75/3.97          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.75/3.97      inference('eq_fact', [status(thm)], ['30'])).
% 3.75/3.97  thf('32', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 3.75/3.97         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 3.75/3.97          | ~ (r2_hidden @ X2 @ X4)
% 3.75/3.97          | ~ (r2_hidden @ X0 @ X1))),
% 3.75/3.97      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.75/3.97  thf('33', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.75/3.97         (((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.75/3.97          | ~ (r2_hidden @ X3 @ X2)
% 3.75/3.97          | (r2_hidden @ 
% 3.75/3.97             (k4_tarski @ X3 @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))) @ 
% 3.75/3.97             (k2_zfmisc_1 @ X2 @ X0)))),
% 3.75/3.97      inference('sup-', [status(thm)], ['31', '32'])).
% 3.75/3.97  thf('34', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.75/3.97         (((X0) = (k1_xboole_0))
% 3.75/3.97          | (r2_hidden @ 
% 3.75/3.97             (k4_tarski @ (sk_C @ X0 @ k1_xboole_0) @ 
% 3.75/3.97              (sk_C_1 @ X1 @ (k2_zfmisc_1 @ X2 @ X1))) @ 
% 3.75/3.97             (k2_zfmisc_1 @ X0 @ X1))
% 3.75/3.97          | ((X1) = (k2_relat_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.75/3.97      inference('sup-', [status(thm)], ['27', '33'])).
% 3.75/3.97  thf('35', plain,
% 3.75/3.97      (![X17 : $i, X20 : $i, X21 : $i]:
% 3.75/3.97         (((X20) = (k2_relat_1 @ X17))
% 3.75/3.97          | ~ (r2_hidden @ (k4_tarski @ X21 @ (sk_C_1 @ X20 @ X17)) @ X17)
% 3.75/3.97          | ~ (r2_hidden @ (sk_C_1 @ X20 @ X17) @ X20))),
% 3.75/3.97      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.75/3.97  thf('36', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         (((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.75/3.97          | ((X1) = (k1_xboole_0))
% 3.75/3.97          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 3.75/3.97          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.75/3.97      inference('sup-', [status(thm)], ['34', '35'])).
% 3.75/3.97  thf('37', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         (~ (r2_hidden @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 3.75/3.97          | ((X1) = (k1_xboole_0))
% 3.75/3.97          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.75/3.97      inference('simplify', [status(thm)], ['36'])).
% 3.75/3.97  thf('38', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 3.75/3.97          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.75/3.97      inference('eq_fact', [status(thm)], ['30'])).
% 3.75/3.97  thf('39', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         (((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.75/3.97          | ((X1) = (k1_xboole_0)))),
% 3.75/3.97      inference('clc', [status(thm)], ['37', '38'])).
% 3.75/3.97  thf(t195_relat_1, conjecture,
% 3.75/3.97    (![A:$i,B:$i]:
% 3.75/3.97     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 3.75/3.97          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 3.75/3.97               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 3.75/3.97  thf(zf_stmt_0, negated_conjecture,
% 3.75/3.97    (~( ![A:$i,B:$i]:
% 3.75/3.97        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 3.75/3.97             ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 3.75/3.97                  ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ) )),
% 3.75/3.97    inference('cnf.neg', [status(esa)], [t195_relat_1])).
% 3.75/3.97  thf('40', plain,
% 3.75/3.97      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A))
% 3.75/3.97        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B)))),
% 3.75/3.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.97  thf('41', plain,
% 3.75/3.97      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B)))
% 3.75/3.97         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))))),
% 3.75/3.97      inference('split', [status(esa)], ['40'])).
% 3.75/3.97  thf('42', plain,
% 3.75/3.97      (![X10 : $i, X13 : $i]:
% 3.75/3.97         (((X13) = (k1_relat_1 @ X10))
% 3.75/3.97          | (r2_hidden @ 
% 3.75/3.97             (k4_tarski @ (sk_C @ X13 @ X10) @ (sk_D @ X13 @ X10)) @ X10)
% 3.75/3.97          | (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 3.75/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.75/3.97  thf('43', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.75/3.97         ((r2_hidden @ X0 @ X1)
% 3.75/3.97          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 3.75/3.97      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 3.75/3.97  thf('44', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 3.75/3.97          | ((X2) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.75/3.97          | (r2_hidden @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X1))),
% 3.75/3.97      inference('sup-', [status(thm)], ['42', '43'])).
% 3.75/3.97  thf('45', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ X0 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)
% 3.75/3.97          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 3.75/3.97      inference('eq_fact', [status(thm)], ['44'])).
% 3.75/3.97  thf('46', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.75/3.97         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 3.75/3.97          | ~ (r2_hidden @ X2 @ X1)
% 3.75/3.97          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ X0 @ k1_xboole_0)) @ 
% 3.75/3.97             (k2_zfmisc_1 @ X1 @ X0)))),
% 3.75/3.97      inference('sup-', [status(thm)], ['10', '11'])).
% 3.75/3.97  thf('47', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.75/3.97      inference('clc', [status(thm)], ['24', '25'])).
% 3.75/3.97  thf('48', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.75/3.97         (((X0) = (k1_xboole_0))
% 3.75/3.97          | ~ (r2_hidden @ X2 @ X1)
% 3.75/3.97          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ X0 @ k1_xboole_0)) @ 
% 3.75/3.97             (k2_zfmisc_1 @ X1 @ X0)))),
% 3.75/3.97      inference('demod', [status(thm)], ['46', '47'])).
% 3.75/3.97  thf('49', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.75/3.97         (((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 3.75/3.97          | (r2_hidden @ 
% 3.75/3.97             (k4_tarski @ (sk_C @ X0 @ (k2_zfmisc_1 @ X0 @ X1)) @ 
% 3.75/3.97              (sk_C @ X2 @ k1_xboole_0)) @ 
% 3.75/3.97             (k2_zfmisc_1 @ X0 @ X2))
% 3.75/3.97          | ((X2) = (k1_xboole_0)))),
% 3.75/3.97      inference('sup-', [status(thm)], ['45', '48'])).
% 3.75/3.97  thf('50', plain,
% 3.75/3.97      (![X10 : $i, X13 : $i, X14 : $i]:
% 3.75/3.97         (((X13) = (k1_relat_1 @ X10))
% 3.75/3.97          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X13 @ X10) @ X14) @ X10)
% 3.75/3.97          | ~ (r2_hidden @ (sk_C @ X13 @ X10) @ X13))),
% 3.75/3.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.75/3.97  thf('51', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         (((X0) = (k1_xboole_0))
% 3.75/3.97          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.75/3.97          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X1)
% 3.75/3.97          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.75/3.97      inference('sup-', [status(thm)], ['49', '50'])).
% 3.75/3.97  thf('52', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         (~ (r2_hidden @ (sk_C @ X1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X1)
% 3.75/3.97          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.75/3.97          | ((X0) = (k1_xboole_0)))),
% 3.75/3.97      inference('simplify', [status(thm)], ['51'])).
% 3.75/3.97  thf('53', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         ((r2_hidden @ (sk_C @ X0 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)
% 3.75/3.97          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 3.75/3.97      inference('eq_fact', [status(thm)], ['44'])).
% 3.75/3.97  thf('54', plain,
% 3.75/3.97      (![X0 : $i, X1 : $i]:
% 3.75/3.97         (((X0) = (k1_xboole_0))
% 3.75/3.97          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.75/3.97      inference('clc', [status(thm)], ['52', '53'])).
% 3.75/3.97  thf('55', plain,
% 3.75/3.97      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_A)))
% 3.75/3.97         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))))),
% 3.75/3.97      inference('split', [status(esa)], ['40'])).
% 3.75/3.97  thf('56', plain,
% 3.75/3.97      (((((sk_A) != (sk_A)) | ((sk_B) = (k1_xboole_0))))
% 3.75/3.97         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))))),
% 3.75/3.97      inference('sup-', [status(thm)], ['54', '55'])).
% 3.75/3.97  thf('57', plain,
% 3.75/3.97      ((((sk_B) = (k1_xboole_0)))
% 3.75/3.97         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A))))),
% 3.75/3.97      inference('simplify', [status(thm)], ['56'])).
% 3.75/3.97  thf('58', plain, (((sk_B) != (k1_xboole_0))),
% 3.75/3.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.97  thf('59', plain, ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A)))),
% 3.75/3.97      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 3.75/3.97  thf('60', plain,
% 3.75/3.97      (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B))) | 
% 3.75/3.97       ~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_A)))),
% 3.75/3.97      inference('split', [status(esa)], ['40'])).
% 3.75/3.97  thf('61', plain, (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_B)))),
% 3.75/3.97      inference('sat_resolution*', [status(thm)], ['59', '60'])).
% 3.75/3.97  thf('62', plain, (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) != (sk_B))),
% 3.75/3.97      inference('simpl_trail', [status(thm)], ['41', '61'])).
% 3.75/3.97  thf('63', plain, ((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 3.75/3.97      inference('sup-', [status(thm)], ['39', '62'])).
% 3.75/3.97  thf('64', plain, (((sk_A) = (k1_xboole_0))),
% 3.75/3.97      inference('simplify', [status(thm)], ['63'])).
% 3.75/3.97  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 3.75/3.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.97  thf('66', plain, ($false),
% 3.75/3.97      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 3.75/3.97  
% 3.75/3.97  % SZS output end Refutation
% 3.75/3.97  
% 3.80/3.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
