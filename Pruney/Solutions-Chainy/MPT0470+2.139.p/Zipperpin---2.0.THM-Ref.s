%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vrpXAJ8SSq

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:46 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 157 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  747 (1678 expanded)
%              Number of equality atoms :   50 ( 129 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('1',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X23: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X23 ) @ ( sk_C_2 @ X23 ) ) @ X23 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('5',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( ( k5_relat_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 )
      | ( ( k5_relat_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k5_relat_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k5_relat_1 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','22'])).

thf('24',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X11 @ X12 ) @ ( sk_E @ X13 @ X11 @ X12 ) ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X11 @ X12 ) @ ( sk_F @ X13 @ X11 @ X12 ) ) @ X12 )
      | ( X13
        = ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k5_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X2 @ X1 ) @ ( sk_F @ X0 @ X2 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_relat_1 @ sk_A )
        | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['36','37'])).

thf('40',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ~ ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ X0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','49'])).

thf('51',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','50'])).

thf('52',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('53',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vrpXAJ8SSq
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.13  % Solved by: fo/fo7.sh
% 0.89/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.13  % done 576 iterations in 0.673s
% 0.89/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.13  % SZS output start Refutation
% 0.89/1.13  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.89/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.13  thf(sk_B_type, type, sk_B: $i > $i).
% 0.89/1.13  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.89/1.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.89/1.13  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.89/1.13  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.89/1.13  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.89/1.13  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.89/1.13  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.89/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.13  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.89/1.13  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.89/1.13  thf('0', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.89/1.13      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.89/1.13  thf(t62_relat_1, conjecture,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( v1_relat_1 @ A ) =>
% 0.89/1.13       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.89/1.13         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.89/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.13    (~( ![A:$i]:
% 0.89/1.13        ( ( v1_relat_1 @ A ) =>
% 0.89/1.13          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.89/1.13            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.89/1.13    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.89/1.13  thf('1', plain, ((v1_relat_1 @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(dt_k5_relat_1, axiom,
% 0.89/1.13    (![A:$i,B:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.89/1.13       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.89/1.13  thf('2', plain,
% 0.89/1.13      (![X19 : $i, X20 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X19)
% 0.89/1.13          | ~ (v1_relat_1 @ X20)
% 0.89/1.13          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.89/1.13  thf(t56_relat_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( v1_relat_1 @ A ) =>
% 0.89/1.13       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.89/1.13         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.89/1.13  thf('3', plain,
% 0.89/1.13      (![X23 : $i]:
% 0.89/1.13         ((r2_hidden @ (k4_tarski @ (sk_B @ X23) @ (sk_C_2 @ X23)) @ X23)
% 0.89/1.13          | ((X23) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_relat_1 @ X23))),
% 0.89/1.13      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.89/1.13  thf(d8_relat_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( v1_relat_1 @ A ) =>
% 0.89/1.13       ( ![B:$i]:
% 0.89/1.13         ( ( v1_relat_1 @ B ) =>
% 0.89/1.13           ( ![C:$i]:
% 0.89/1.13             ( ( v1_relat_1 @ C ) =>
% 0.89/1.13               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.89/1.13                 ( ![D:$i,E:$i]:
% 0.89/1.13                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.89/1.13                     ( ?[F:$i]:
% 0.89/1.13                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.89/1.13                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.89/1.13  thf('4', plain,
% 0.89/1.13      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X17 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X11)
% 0.89/1.13          | ((X13) != (k5_relat_1 @ X12 @ X11))
% 0.89/1.13          | (r2_hidden @ 
% 0.89/1.13             (k4_tarski @ (sk_F_1 @ X17 @ X14 @ X11 @ X12) @ X17) @ X11)
% 0.89/1.13          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ X13)
% 0.89/1.13          | ~ (v1_relat_1 @ X13)
% 0.89/1.13          | ~ (v1_relat_1 @ X12))),
% 0.89/1.13      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.89/1.13  thf('5', plain,
% 0.89/1.13      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X12)
% 0.89/1.13          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.89/1.13          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 0.89/1.13          | (r2_hidden @ 
% 0.89/1.13             (k4_tarski @ (sk_F_1 @ X17 @ X14 @ X11 @ X12) @ X17) @ X11)
% 0.89/1.13          | ~ (v1_relat_1 @ X11))),
% 0.89/1.13      inference('simplify', [status(thm)], ['4'])).
% 0.89/1.13  thf('6', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.89/1.13          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | (r2_hidden @ 
% 0.89/1.13             (k4_tarski @ 
% 0.89/1.13              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.89/1.13               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.89/1.13              (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.89/1.13             X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ X1))),
% 0.89/1.13      inference('sup-', [status(thm)], ['3', '5'])).
% 0.89/1.13  thf('7', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X1)
% 0.89/1.13          | (r2_hidden @ 
% 0.89/1.13             (k4_tarski @ 
% 0.89/1.13              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.89/1.13               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.89/1.13              (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.89/1.13             X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.89/1.13      inference('simplify', [status(thm)], ['6'])).
% 0.89/1.13  thf('8', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X1)
% 0.89/1.13          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | (r2_hidden @ 
% 0.89/1.13             (k4_tarski @ 
% 0.89/1.13              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.89/1.13               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.89/1.13              (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.89/1.13             X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X1))),
% 0.89/1.13      inference('sup-', [status(thm)], ['2', '7'])).
% 0.89/1.13  thf('9', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         ((r2_hidden @ 
% 0.89/1.13           (k4_tarski @ 
% 0.89/1.13            (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.89/1.13             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.89/1.13            (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.89/1.13           X0)
% 0.89/1.13          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_relat_1 @ X1)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['8'])).
% 0.89/1.13  thf(t7_tarski, axiom,
% 0.89/1.13    (![A:$i,B:$i]:
% 0.89/1.13     ( ~( ( r2_hidden @ A @ B ) & 
% 0.89/1.13          ( ![C:$i]:
% 0.89/1.13            ( ~( ( r2_hidden @ C @ B ) & 
% 0.89/1.13                 ( ![D:$i]:
% 0.89/1.13                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.89/1.13  thf('10', plain,
% 0.89/1.13      (![X8 : $i, X9 : $i]:
% 0.89/1.13         (~ (r2_hidden @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9) @ X9))),
% 0.89/1.13      inference('cnf', [status(esa)], [t7_tarski])).
% 0.89/1.13  thf('11', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X1)
% 0.89/1.13          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.89/1.13          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.13  thf('12', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((r2_hidden @ (sk_C_1 @ X0) @ X0)
% 0.89/1.13          | ((k5_relat_1 @ sk_A @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['1', '11'])).
% 0.89/1.13  thf('13', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         ((r2_hidden @ (sk_C_1 @ X0) @ X0)
% 0.89/1.13          | ((k5_relat_1 @ sk_A @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['1', '11'])).
% 0.89/1.13  thf(t3_xboole_0, axiom,
% 0.89/1.13    (![A:$i,B:$i]:
% 0.89/1.13     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.89/1.13            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.89/1.13       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.89/1.13            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.89/1.13  thf('14', plain,
% 0.89/1.13      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.89/1.13         (~ (r2_hidden @ X2 @ X0)
% 0.89/1.13          | ~ (r2_hidden @ X2 @ X3)
% 0.89/1.13          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.89/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.89/1.13  thf('15', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ sk_A @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.89/1.13          | ~ (r2_hidden @ (sk_C_1 @ X0) @ X1))),
% 0.89/1.13      inference('sup-', [status(thm)], ['13', '14'])).
% 0.89/1.13  thf('16', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ sk_A @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ sk_A @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['12', '15'])).
% 0.89/1.13  thf('17', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (r1_xboole_0 @ X0 @ X0)
% 0.89/1.13          | ((k5_relat_1 @ sk_A @ X0) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['16'])).
% 0.89/1.13  thf('18', plain,
% 0.89/1.13      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.89/1.13        | ((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['0', '17'])).
% 0.89/1.13  thf(t113_zfmisc_1, axiom,
% 0.89/1.13    (![A:$i,B:$i]:
% 0.89/1.13     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.89/1.13       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.89/1.13  thf('19', plain,
% 0.89/1.13      (![X6 : $i, X7 : $i]:
% 0.89/1.13         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.89/1.13      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.89/1.13  thf('20', plain,
% 0.89/1.13      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.89/1.13      inference('simplify', [status(thm)], ['19'])).
% 0.89/1.13  thf(fc6_relat_1, axiom,
% 0.89/1.13    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.13  thf('21', plain,
% 0.89/1.13      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.13  thf('22', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.89/1.13      inference('sup+', [status(thm)], ['20', '21'])).
% 0.89/1.13  thf('23', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.13      inference('demod', [status(thm)], ['18', '22'])).
% 0.89/1.13  thf('24', plain,
% 0.89/1.13      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.89/1.13        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('25', plain,
% 0.89/1.13      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.89/1.13         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.89/1.13      inference('split', [status(esa)], ['24'])).
% 0.89/1.13  thf('26', plain,
% 0.89/1.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X11)
% 0.89/1.13          | (r2_hidden @ 
% 0.89/1.13             (k4_tarski @ (sk_D @ X13 @ X11 @ X12) @ (sk_E @ X13 @ X11 @ X12)) @ 
% 0.89/1.13             X13)
% 0.89/1.13          | (r2_hidden @ 
% 0.89/1.13             (k4_tarski @ (sk_D @ X13 @ X11 @ X12) @ (sk_F @ X13 @ X11 @ X12)) @ 
% 0.89/1.13             X12)
% 0.89/1.13          | ((X13) = (k5_relat_1 @ X12 @ X11))
% 0.89/1.13          | ~ (v1_relat_1 @ X13)
% 0.89/1.13          | ~ (v1_relat_1 @ X12))),
% 0.89/1.13      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.89/1.13  thf('27', plain,
% 0.89/1.13      (![X8 : $i, X9 : $i]:
% 0.89/1.13         (~ (r2_hidden @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9) @ X9))),
% 0.89/1.13      inference('cnf', [status(esa)], [t7_tarski])).
% 0.89/1.13  thf('28', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X1)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((X0) = (k5_relat_1 @ X1 @ X2))
% 0.89/1.13          | (r2_hidden @ 
% 0.89/1.13             (k4_tarski @ (sk_D @ X0 @ X2 @ X1) @ (sk_F @ X0 @ X2 @ X1)) @ X1)
% 0.89/1.13          | ~ (v1_relat_1 @ X2)
% 0.89/1.13          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['26', '27'])).
% 0.89/1.13  thf('29', plain,
% 0.89/1.13      (![X8 : $i, X9 : $i]:
% 0.89/1.13         (~ (r2_hidden @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9) @ X9))),
% 0.89/1.13      inference('cnf', [status(esa)], [t7_tarski])).
% 0.89/1.13  thf('30', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((r2_hidden @ (sk_C_1 @ X2) @ X2)
% 0.89/1.13          | ~ (v1_relat_1 @ X1)
% 0.89/1.13          | ((X2) = (k5_relat_1 @ X0 @ X1))
% 0.89/1.13          | ~ (v1_relat_1 @ X2)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['28', '29'])).
% 0.89/1.13  thf('31', plain,
% 0.89/1.13      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.89/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.13      inference('split', [status(esa)], ['24'])).
% 0.89/1.13  thf('32', plain,
% 0.89/1.13      ((![X0 : $i]:
% 0.89/1.13          (((X0) != (k1_xboole_0))
% 0.89/1.13           | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.89/1.13           | ~ (v1_relat_1 @ k1_xboole_0)
% 0.89/1.13           | ~ (v1_relat_1 @ X0)
% 0.89/1.13           | ~ (v1_relat_1 @ sk_A)
% 0.89/1.13           | (r2_hidden @ (sk_C_1 @ X0) @ X0)))
% 0.89/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['30', '31'])).
% 0.89/1.13  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.89/1.13      inference('sup+', [status(thm)], ['20', '21'])).
% 0.89/1.13  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('35', plain,
% 0.89/1.13      ((![X0 : $i]:
% 0.89/1.13          (((X0) != (k1_xboole_0))
% 0.89/1.13           | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.89/1.13           | ~ (v1_relat_1 @ X0)
% 0.89/1.13           | (r2_hidden @ (sk_C_1 @ X0) @ X0)))
% 0.89/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.13      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.89/1.13  thf('36', plain,
% 0.89/1.13      (((~ (v1_relat_1 @ k1_xboole_0)
% 0.89/1.13         | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)))
% 0.89/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.13      inference('simplify', [status(thm)], ['35'])).
% 0.89/1.13  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.89/1.13      inference('sup+', [status(thm)], ['20', '21'])).
% 0.89/1.13  thf('38', plain,
% 0.89/1.13      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0))
% 0.89/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.13      inference('simplify_reflect+', [status(thm)], ['36', '37'])).
% 0.89/1.13  thf('39', plain,
% 0.89/1.13      (((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0))
% 0.89/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.13      inference('simplify_reflect+', [status(thm)], ['36', '37'])).
% 0.89/1.13  thf('40', plain,
% 0.89/1.13      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.89/1.13         (~ (r2_hidden @ X2 @ X0)
% 0.89/1.13          | ~ (r2_hidden @ X2 @ X3)
% 0.89/1.13          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.89/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.89/1.13  thf('41', plain,
% 0.89/1.13      ((![X0 : $i]:
% 0.89/1.13          (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.89/1.13           | ~ (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ X0)))
% 0.89/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['39', '40'])).
% 0.89/1.13  thf('42', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.89/1.13      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.89/1.13  thf('43', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.89/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.89/1.13  thf('44', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.89/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.89/1.13  thf('45', plain,
% 0.89/1.13      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.89/1.13         (~ (r2_hidden @ X2 @ X0)
% 0.89/1.13          | ~ (r2_hidden @ X2 @ X3)
% 0.89/1.13          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.89/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.89/1.13  thf('46', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((r1_xboole_0 @ X0 @ X1)
% 0.89/1.13          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.89/1.13          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.89/1.13      inference('sup-', [status(thm)], ['44', '45'])).
% 0.89/1.13  thf('47', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         ((r1_xboole_0 @ X0 @ X1)
% 0.89/1.13          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.89/1.13          | (r1_xboole_0 @ X0 @ X1))),
% 0.89/1.13      inference('sup-', [status(thm)], ['43', '46'])).
% 0.89/1.13  thf('48', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.89/1.13      inference('simplify', [status(thm)], ['47'])).
% 0.89/1.13  thf('49', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.89/1.13      inference('sup-', [status(thm)], ['42', '48'])).
% 0.89/1.13  thf('50', plain,
% 0.89/1.13      ((![X0 : $i]: ~ (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ X0))
% 0.89/1.13         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.89/1.13      inference('demod', [status(thm)], ['41', '49'])).
% 0.89/1.13  thf('51', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['38', '50'])).
% 0.89/1.13  thf('52', plain,
% 0.89/1.13      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.89/1.13       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.89/1.13      inference('split', [status(esa)], ['24'])).
% 0.89/1.13  thf('53', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.89/1.13      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.89/1.13  thf('54', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.89/1.13      inference('simpl_trail', [status(thm)], ['25', '53'])).
% 0.89/1.13  thf('55', plain, ($false),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['23', '54'])).
% 0.89/1.13  
% 0.89/1.13  % SZS output end Refutation
% 0.89/1.13  
% 0.98/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
