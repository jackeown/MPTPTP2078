%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s4FTp4Si8t

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:47 EST 2020

% Result     : Theorem 43.74s
% Output     : Refutation 43.74s
% Verified   : 
% Statistics : Number of formulae       :  257 (10924 expanded)
%              Number of leaves         :   24 (3025 expanded)
%              Depth                    :   67
%              Number of atoms          : 2756 (130293 expanded)
%              Number of equality atoms :  353 (16037 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('3',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('4',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('8',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != ( k2_zfmisc_1 @ X26 @ X27 ) )
      | ( X25 = X26 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( X1
        = ( k3_xboole_0 @ sk_A @ sk_C_1 ) )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(eq_res,[status(thm)],['10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('22',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('23',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != ( k2_zfmisc_1 @ X26 @ X27 ) )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = X0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = sk_B_1 ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,
    ( ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
        = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
        = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
        = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,
    ( ( ( ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ sk_D )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','36'])).

thf('38',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ sk_D )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ sk_D )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['20','40'])).

thf('42',plain,
    ( ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ k1_xboole_0 @ sk_D )
        | ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ k1_xboole_0 @ sk_D )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','48'])).

thf('50',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_D )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( r1_xboole_0 @ k1_xboole_0 @ sk_D )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('58',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
        | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
        | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','63'])).

thf('65',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','66'])).

thf('68',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('69',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('70',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('71',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != ( k2_zfmisc_1 @ X26 @ X27 ) )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( X0
        = ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1
      = ( k3_xboole_0 @ sk_B_1 @ sk_D ) ) ),
    inference(eq_res,[status(thm)],['72'])).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('84',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('85',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('88',plain,
    ( ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
        = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('90',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
        = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
        = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('93',plain,
    ( ( ( ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ sk_D )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['82','93'])).

thf('95',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('96',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ sk_D )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ sk_D )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('101',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','103'])).

thf('105',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('112',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = sk_B_1 ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('113',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('114',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != ( k2_zfmisc_1 @ X26 @ X27 ) )
      | ( X25 = X26 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = X1 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = sk_A ) ),
    inference(eq_res,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = sk_A ) ),
    inference(eq_res,[status(thm)],['115'])).

thf('118',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('119',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('120',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('122',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ k1_xboole_0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = sk_A )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['117','122'])).

thf('124',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('125',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('126',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('127',plain,
    ( ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ k1_xboole_0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ k1_xboole_0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = X0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('130',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('132',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('133',plain,
    ( ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
       != ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('136',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( r1_xboole_0 @ sk_B_1 @ sk_D )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('139',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
          = k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ X1 ) @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('141',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('142',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
          = k1_xboole_0 )
        | ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) @ ( k3_xboole_0 @ X1 @ X0 ) )
          = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
          = k1_xboole_0 )
        | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
          = sk_A )
        | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
          = k1_xboole_0 )
        | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
          = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['116','145'])).

thf('147',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('148',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('149',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('150',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
          = k1_xboole_0 )
        | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
          = k1_xboole_0 )
        | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
          = k1_xboole_0 )
        | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
          = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
          = k1_xboole_0 )
        | ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
          = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('153',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
          = k1_xboole_0 )
        | ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        | ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
          = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['112','154'])).

thf('156',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('157',plain,
    ( ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('159',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['157','160'])).

thf('162',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('163',plain,
    ( ( ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('165',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
      | ( r1_xboole_0 @ sk_B_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( r1_xboole_0 @ sk_B_1 @ sk_D )
      | ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('168',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('170',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['111','170'])).

thf('172',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('173',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('175',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['110','175'])).

thf('177',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','176'])).

thf('178',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('179',plain,(
    r1_tarski @ sk_B_1 @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('181',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['67','181'])).

thf('183',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('184',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = sk_A ) ),
    inference(eq_res,[status(thm)],['115'])).

thf('185',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('186',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('187',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('189',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_D ) )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ k1_xboole_0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = sk_A )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['184','189'])).

thf('191',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('192',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('193',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('194',plain,
    ( ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ k1_xboole_0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['190','191','192','193'])).

thf('195',plain,
    ( ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 ) @ k1_xboole_0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = X0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('197',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('199',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('200',plain,
    ( ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
       != ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('203',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( r1_xboole_0 @ sk_B_1 @ sk_D )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['179','180'])).

thf('206',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_D )
    | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('211',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('213',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['179','180'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['208','215'])).

thf('217',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['183','216'])).

thf('218',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('219',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['179','180'])).

thf('222',plain,(
    ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['220','221'])).

thf('223',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['217','222'])).

thf('224',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('225',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_C_1 )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('227',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('229',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ k1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    r1_tarski @ k1_xboole_0 @ sk_C_1 ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    $false ),
    inference(demod,[status(thm)],['182','230'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s4FTp4Si8t
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 43.74/43.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 43.74/43.95  % Solved by: fo/fo7.sh
% 43.74/43.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 43.74/43.95  % done 4188 iterations in 43.476s
% 43.74/43.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 43.74/43.95  % SZS output start Refutation
% 43.74/43.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 43.74/43.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 43.74/43.95  thf(sk_A_type, type, sk_A: $i).
% 43.74/43.95  thf(sk_B_type, type, sk_B: $i > $i).
% 43.74/43.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 43.74/43.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 43.74/43.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 43.74/43.95  thf(sk_D_type, type, sk_D: $i).
% 43.74/43.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 43.74/43.95  thf(sk_B_1_type, type, sk_B_1: $i).
% 43.74/43.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 43.74/43.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 43.74/43.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 43.74/43.95  thf(t138_zfmisc_1, conjecture,
% 43.74/43.95    (![A:$i,B:$i,C:$i,D:$i]:
% 43.74/43.95     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 43.74/43.95       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 43.74/43.95         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 43.74/43.95  thf(zf_stmt_0, negated_conjecture,
% 43.74/43.95    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 43.74/43.95        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 43.74/43.95          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 43.74/43.95            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 43.74/43.95    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 43.74/43.95  thf('0', plain,
% 43.74/43.95      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B_1 @ sk_D))),
% 43.74/43.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.74/43.95  thf('1', plain,
% 43.74/43.95      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('split', [status(esa)], ['0'])).
% 43.74/43.95  thf(t7_xboole_0, axiom,
% 43.74/43.95    (![A:$i]:
% 43.74/43.95     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 43.74/43.95          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 43.74/43.95  thf('2', plain,
% 43.74/43.95      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 43.74/43.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.74/43.95  thf('3', plain,
% 43.74/43.95      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 43.74/43.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.74/43.95  thf('4', plain,
% 43.74/43.95      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 43.74/43.95        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 43.74/43.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.74/43.95  thf(t28_xboole_1, axiom,
% 43.74/43.95    (![A:$i,B:$i]:
% 43.74/43.95     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 43.74/43.95  thf('5', plain,
% 43.74/43.95      (![X13 : $i, X14 : $i]:
% 43.74/43.95         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 43.74/43.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 43.74/43.95  thf('6', plain,
% 43.74/43.95      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 43.74/43.95         (k2_zfmisc_1 @ sk_C_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 43.74/43.95      inference('sup-', [status(thm)], ['4', '5'])).
% 43.74/43.95  thf(t123_zfmisc_1, axiom,
% 43.74/43.95    (![A:$i,B:$i,C:$i,D:$i]:
% 43.74/43.95     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 43.74/43.95       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 43.74/43.95  thf('7', plain,
% 43.74/43.95      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 43.74/43.95         ((k2_zfmisc_1 @ (k3_xboole_0 @ X16 @ X18) @ (k3_xboole_0 @ X17 @ X19))
% 43.74/43.95           = (k3_xboole_0 @ (k2_zfmisc_1 @ X16 @ X17) @ 
% 43.74/43.95              (k2_zfmisc_1 @ X18 @ X19)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 43.74/43.95  thf('8', plain,
% 43.74/43.95      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 43.74/43.95         (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 43.74/43.95      inference('demod', [status(thm)], ['6', '7'])).
% 43.74/43.95  thf(t134_zfmisc_1, axiom,
% 43.74/43.95    (![A:$i,B:$i,C:$i,D:$i]:
% 43.74/43.95     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 43.74/43.95       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 43.74/43.95         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 43.74/43.95  thf('9', plain,
% 43.74/43.95      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 43.74/43.95         (((X24) = (k1_xboole_0))
% 43.74/43.95          | ((X25) = (k1_xboole_0))
% 43.74/43.95          | ((k2_zfmisc_1 @ X25 @ X24) != (k2_zfmisc_1 @ X26 @ X27))
% 43.74/43.95          | ((X25) = (X26)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 43.74/43.95  thf('10', plain,
% 43.74/43.95      (![X0 : $i, X1 : $i]:
% 43.74/43.95         (((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.74/43.95          | ((X1) = (k3_xboole_0 @ sk_A @ sk_C_1))
% 43.74/43.95          | ((X1) = (k1_xboole_0))
% 43.74/43.95          | ((X0) = (k1_xboole_0)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['8', '9'])).
% 43.74/43.95  thf('11', plain,
% 43.74/43.95      ((((sk_B_1) = (k1_xboole_0))
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('eq_res', [status(thm)], ['10'])).
% 43.74/43.95  thf(t100_xboole_1, axiom,
% 43.74/43.95    (![A:$i,B:$i]:
% 43.74/43.95     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 43.74/43.95  thf('12', plain,
% 43.74/43.95      (![X11 : $i, X12 : $i]:
% 43.74/43.95         ((k4_xboole_0 @ X11 @ X12)
% 43.74/43.95           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 43.74/43.95  thf('13', plain,
% 43.74/43.95      ((((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_A))
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | ((sk_B_1) = (k1_xboole_0)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['11', '12'])).
% 43.74/43.95  thf(t92_xboole_1, axiom,
% 43.74/43.95    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 43.74/43.95  thf('14', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 43.74/43.95  thf('15', plain,
% 43.74/43.95      ((((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | ((sk_B_1) = (k1_xboole_0)))),
% 43.74/43.95      inference('demod', [status(thm)], ['13', '14'])).
% 43.74/43.95  thf(l32_xboole_1, axiom,
% 43.74/43.95    (![A:$i,B:$i]:
% 43.74/43.95     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 43.74/43.95  thf('16', plain,
% 43.74/43.95      (![X8 : $i, X9 : $i]:
% 43.74/43.95         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 43.74/43.95  thf('17', plain,
% 43.74/43.95      ((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95        | ((sk_B_1) = (k1_xboole_0))
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | (r1_tarski @ sk_A @ sk_C_1))),
% 43.74/43.95      inference('sup-', [status(thm)], ['15', '16'])).
% 43.74/43.95  thf('18', plain,
% 43.74/43.95      (((r1_tarski @ sk_A @ sk_C_1)
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | ((sk_B_1) = (k1_xboole_0)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['17'])).
% 43.74/43.95  thf('19', plain,
% 43.74/43.95      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('split', [status(esa)], ['0'])).
% 43.74/43.95  thf('20', plain,
% 43.74/43.95      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['18', '19'])).
% 43.74/43.95  thf('21', plain,
% 43.74/43.95      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['18', '19'])).
% 43.74/43.95  thf('22', plain,
% 43.74/43.95      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['18', '19'])).
% 43.74/43.95  thf('23', plain,
% 43.74/43.95      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 43.74/43.95         (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 43.74/43.95      inference('demod', [status(thm)], ['6', '7'])).
% 43.74/43.95  thf('24', plain,
% 43.74/43.95      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 43.74/43.95         (((X24) = (k1_xboole_0))
% 43.74/43.95          | ((X25) = (k1_xboole_0))
% 43.74/43.95          | ((k2_zfmisc_1 @ X25 @ X24) != (k2_zfmisc_1 @ X26 @ X27))
% 43.74/43.95          | ((X24) = (X27)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 43.74/43.95  thf('25', plain,
% 43.74/43.95      (![X0 : $i, X1 : $i]:
% 43.74/43.95         (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k2_zfmisc_1 @ X1 @ X0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (X0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['23', '24'])).
% 43.74/43.95  thf('26', plain,
% 43.74/43.95      ((((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1)))),
% 43.74/43.95      inference('eq_res', [status(thm)], ['25'])).
% 43.74/43.95  thf('27', plain,
% 43.74/43.95      ((((sk_B_1) != (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0)))),
% 43.74/43.95      inference('eq_fact', [status(thm)], ['26'])).
% 43.74/43.95  thf('28', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['22', '27'])).
% 43.74/43.95  thf('29', plain,
% 43.74/43.95      (((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['28'])).
% 43.74/43.95  thf('30', plain,
% 43.74/43.95      (![X11 : $i, X12 : $i]:
% 43.74/43.95         ((k4_xboole_0 @ X11 @ X12)
% 43.74/43.95           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 43.74/43.95  thf('31', plain,
% 43.74/43.95      (((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['29', '30'])).
% 43.74/43.95  thf(d7_xboole_0, axiom,
% 43.74/43.95    (![A:$i,B:$i]:
% 43.74/43.95     ( ( r1_xboole_0 @ A @ B ) <=>
% 43.74/43.95       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 43.74/43.95  thf('32', plain,
% 43.74/43.95      (![X0 : $i, X2 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.74/43.95  thf('33', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | ((k4_xboole_0 @ sk_B_1 @ sk_D)
% 43.74/43.95             = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ sk_A @ sk_C_1))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['31', '32'])).
% 43.74/43.95  thf('34', plain,
% 43.74/43.95      ((((r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | ((k4_xboole_0 @ sk_B_1 @ sk_D)
% 43.74/43.95             = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['33'])).
% 43.74/43.95  thf('35', plain,
% 43.74/43.95      (![X8 : $i, X9 : $i]:
% 43.74/43.95         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 43.74/43.95  thf('36', plain,
% 43.74/43.95      (((((k5_xboole_0 @ sk_B_1 @ k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | (r1_tarski @ sk_B_1 @ sk_D))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['34', '35'])).
% 43.74/43.95  thf('37', plain,
% 43.74/43.95      (((((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | (r1_tarski @ sk_B_1 @ sk_D)
% 43.74/43.95         | (r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['21', '36'])).
% 43.74/43.95  thf('38', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 43.74/43.95  thf('39', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | (r1_tarski @ sk_B_1 @ sk_D)
% 43.74/43.95         | (r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('demod', [status(thm)], ['37', '38'])).
% 43.74/43.95  thf('40', plain,
% 43.74/43.95      ((((r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | (r1_tarski @ sk_B_1 @ sk_D)
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['39'])).
% 43.74/43.95  thf('41', plain,
% 43.74/43.95      ((((r1_tarski @ k1_xboole_0 @ sk_D)
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ sk_A @ sk_C_1))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['20', '40'])).
% 43.74/43.95  thf('42', plain,
% 43.74/43.95      ((((r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | (r1_tarski @ k1_xboole_0 @ sk_D)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['41'])).
% 43.74/43.95  thf(t127_zfmisc_1, axiom,
% 43.74/43.95    (![A:$i,B:$i,C:$i,D:$i]:
% 43.74/43.95     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 43.74/43.95       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 43.74/43.95  thf('43', plain,
% 43.74/43.95      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ (k2_zfmisc_1 @ X22 @ X23))
% 43.74/43.95          | ~ (r1_xboole_0 @ X20 @ X22))),
% 43.74/43.95      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 43.74/43.95  thf('44', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          ((r1_tarski @ k1_xboole_0 @ sk_D)
% 43.74/43.95           | ((sk_A) = (k1_xboole_0))
% 43.74/43.95           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 43.74/43.95              (k2_zfmisc_1 @ sk_C_1 @ X0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['42', '43'])).
% 43.74/43.95  thf('45', plain,
% 43.74/43.95      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 43.74/43.95         (k2_zfmisc_1 @ sk_C_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 43.74/43.95      inference('sup-', [status(thm)], ['4', '5'])).
% 43.74/43.95  thf(t4_xboole_0, axiom,
% 43.74/43.95    (![A:$i,B:$i]:
% 43.74/43.95     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 43.74/43.95            ( r1_xboole_0 @ A @ B ) ) ) & 
% 43.74/43.95       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 43.74/43.95            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 43.74/43.95  thf('46', plain,
% 43.74/43.95      (![X3 : $i, X5 : $i, X6 : $i]:
% 43.74/43.95         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 43.74/43.95          | ~ (r1_xboole_0 @ X3 @ X6))),
% 43.74/43.95      inference('cnf', [status(esa)], [t4_xboole_0])).
% 43.74/43.95  thf('47', plain,
% 43.74/43.95      (![X0 : $i]:
% 43.74/43.95         (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.74/43.95          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 43.74/43.95               (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['45', '46'])).
% 43.74/43.95  thf('48', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (((sk_A) = (k1_xboole_0))
% 43.74/43.95           | (r1_tarski @ k1_xboole_0 @ sk_D)
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['44', '47'])).
% 43.74/43.95  thf('49', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 43.74/43.95         | (r1_tarski @ k1_xboole_0 @ sk_D)
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['3', '48'])).
% 43.74/43.95  thf('50', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.74/43.95  thf('51', plain,
% 43.74/43.95      ((((r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 43.74/43.95  thf('52', plain,
% 43.74/43.95      (![X13 : $i, X14 : $i]:
% 43.74/43.95         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 43.74/43.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 43.74/43.95  thf('53', plain,
% 43.74/43.95      (((((sk_A) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_D) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['51', '52'])).
% 43.74/43.95  thf('54', plain,
% 43.74/43.95      (![X0 : $i, X2 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.74/43.95  thf('55', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ k1_xboole_0 @ sk_D)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['53', '54'])).
% 43.74/43.95  thf('56', plain,
% 43.74/43.95      ((((r1_xboole_0 @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['55'])).
% 43.74/43.95  thf('57', plain,
% 43.74/43.95      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ (k2_zfmisc_1 @ X22 @ X23))
% 43.74/43.95          | ~ (r1_xboole_0 @ X21 @ X23))),
% 43.74/43.95      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 43.74/43.95  thf('58', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          (((sk_A) = (k1_xboole_0))
% 43.74/43.95           | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ k1_xboole_0) @ 
% 43.74/43.95              (k2_zfmisc_1 @ X0 @ sk_D))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['56', '57'])).
% 43.74/43.95  thf('59', plain,
% 43.74/43.95      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['18', '19'])).
% 43.74/43.95  thf('60', plain,
% 43.74/43.95      (![X0 : $i]:
% 43.74/43.95         (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.74/43.95          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 43.74/43.95               (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['45', '46'])).
% 43.74/43.95  thf('61', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ 
% 43.74/43.95              (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 43.74/43.95           | ((sk_A) = (k1_xboole_0))
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['59', '60'])).
% 43.74/43.95  thf('62', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (((sk_A) = (k1_xboole_0))
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.74/43.95           | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['58', '61'])).
% 43.74/43.95  thf('63', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.74/43.95           | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['62'])).
% 43.74/43.95  thf('64', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['2', '63'])).
% 43.74/43.95  thf('65', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.74/43.95  thf('66', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('67', plain,
% 43.74/43.95      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('demod', [status(thm)], ['1', '66'])).
% 43.74/43.95  thf('68', plain,
% 43.74/43.95      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 43.74/43.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.74/43.95  thf('69', plain,
% 43.74/43.95      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 43.74/43.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.74/43.95  thf('70', plain,
% 43.74/43.95      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 43.74/43.95         (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 43.74/43.95      inference('demod', [status(thm)], ['6', '7'])).
% 43.74/43.95  thf('71', plain,
% 43.74/43.95      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 43.74/43.95         (((X24) = (k1_xboole_0))
% 43.74/43.95          | ((X25) = (k1_xboole_0))
% 43.74/43.95          | ((k2_zfmisc_1 @ X25 @ X24) != (k2_zfmisc_1 @ X26 @ X27))
% 43.74/43.95          | ((X24) = (X27)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 43.74/43.95  thf('72', plain,
% 43.74/43.95      (![X0 : $i, X1 : $i]:
% 43.74/43.95         (((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.74/43.95          | ((X0) = (k3_xboole_0 @ sk_B_1 @ sk_D))
% 43.74/43.95          | ((X1) = (k1_xboole_0))
% 43.74/43.95          | ((X0) = (k1_xboole_0)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['70', '71'])).
% 43.74/43.95  thf('73', plain,
% 43.74/43.95      ((((sk_B_1) = (k1_xboole_0))
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | ((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('eq_res', [status(thm)], ['72'])).
% 43.74/43.95  thf('74', plain,
% 43.74/43.95      (![X11 : $i, X12 : $i]:
% 43.74/43.95         ((k4_xboole_0 @ X11 @ X12)
% 43.74/43.95           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 43.74/43.95  thf('75', plain,
% 43.74/43.95      ((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | ((sk_B_1) = (k1_xboole_0)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['73', '74'])).
% 43.74/43.95  thf('76', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 43.74/43.95  thf('77', plain,
% 43.74/43.95      ((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | ((sk_B_1) = (k1_xboole_0)))),
% 43.74/43.95      inference('demod', [status(thm)], ['75', '76'])).
% 43.74/43.95  thf('78', plain,
% 43.74/43.95      (![X8 : $i, X9 : $i]:
% 43.74/43.95         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 43.74/43.95  thf('79', plain,
% 43.74/43.95      ((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95        | ((sk_B_1) = (k1_xboole_0))
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | (r1_tarski @ sk_B_1 @ sk_D))),
% 43.74/43.95      inference('sup-', [status(thm)], ['77', '78'])).
% 43.74/43.95  thf('80', plain,
% 43.74/43.95      (((r1_tarski @ sk_B_1 @ sk_D)
% 43.74/43.95        | ((sk_A) = (k1_xboole_0))
% 43.74/43.95        | ((sk_B_1) = (k1_xboole_0)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['79'])).
% 43.74/43.95  thf('81', plain,
% 43.74/43.95      ((~ (r1_tarski @ sk_B_1 @ sk_D)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('split', [status(esa)], ['0'])).
% 43.74/43.95  thf('82', plain,
% 43.74/43.95      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['80', '81'])).
% 43.74/43.95  thf('83', plain,
% 43.74/43.95      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['80', '81'])).
% 43.74/43.95  thf('84', plain,
% 43.74/43.95      ((((sk_B_1) != (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0)))),
% 43.74/43.95      inference('eq_fact', [status(thm)], ['26'])).
% 43.74/43.95  thf('85', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['83', '84'])).
% 43.74/43.95  thf('86', plain,
% 43.74/43.95      (((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['85'])).
% 43.74/43.95  thf('87', plain,
% 43.74/43.95      (![X11 : $i, X12 : $i]:
% 43.74/43.95         ((k4_xboole_0 @ X11 @ X12)
% 43.74/43.95           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 43.74/43.95  thf('88', plain,
% 43.74/43.95      (((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['86', '87'])).
% 43.74/43.95  thf('89', plain,
% 43.74/43.95      (![X0 : $i, X2 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.74/43.95  thf('90', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | ((k4_xboole_0 @ sk_B_1 @ sk_D)
% 43.74/43.95             = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ sk_A @ sk_C_1))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['88', '89'])).
% 43.74/43.95  thf('91', plain,
% 43.74/43.95      ((((r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | ((k4_xboole_0 @ sk_B_1 @ sk_D)
% 43.74/43.95             = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['90'])).
% 43.74/43.95  thf('92', plain,
% 43.74/43.95      (![X8 : $i, X9 : $i]:
% 43.74/43.95         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 43.74/43.95  thf('93', plain,
% 43.74/43.95      (((((k5_xboole_0 @ sk_B_1 @ k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | (r1_tarski @ sk_B_1 @ sk_D))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['91', '92'])).
% 43.74/43.95  thf('94', plain,
% 43.74/43.95      (((((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | (r1_tarski @ sk_B_1 @ sk_D)
% 43.74/43.95         | (r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['82', '93'])).
% 43.74/43.95  thf('95', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 43.74/43.95  thf('96', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0))
% 43.74/43.95         | (r1_tarski @ sk_B_1 @ sk_D)
% 43.74/43.95         | (r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('demod', [status(thm)], ['94', '95'])).
% 43.74/43.95  thf('97', plain,
% 43.74/43.95      ((((r1_xboole_0 @ sk_A @ sk_C_1)
% 43.74/43.95         | (r1_tarski @ sk_B_1 @ sk_D)
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['96'])).
% 43.74/43.95  thf('98', plain,
% 43.74/43.95      ((~ (r1_tarski @ sk_B_1 @ sk_D)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('split', [status(esa)], ['0'])).
% 43.74/43.95  thf('99', plain,
% 43.74/43.95      (((((sk_A) = (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('clc', [status(thm)], ['97', '98'])).
% 43.74/43.95  thf('100', plain,
% 43.74/43.95      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ (k2_zfmisc_1 @ X22 @ X23))
% 43.74/43.95          | ~ (r1_xboole_0 @ X20 @ X22))),
% 43.74/43.95      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 43.74/43.95  thf('101', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          (((sk_A) = (k1_xboole_0))
% 43.74/43.95           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 43.74/43.95              (k2_zfmisc_1 @ sk_C_1 @ X0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['99', '100'])).
% 43.74/43.95  thf('102', plain,
% 43.74/43.95      (![X0 : $i]:
% 43.74/43.95         (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.74/43.95          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 43.74/43.95               (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['45', '46'])).
% 43.74/43.95  thf('103', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (((sk_A) = (k1_xboole_0))
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['101', '102'])).
% 43.74/43.95  thf('104', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 43.74/43.95         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['69', '103'])).
% 43.74/43.95  thf('105', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.74/43.95  thf('106', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('107', plain,
% 43.74/43.95      (![X0 : $i]:
% 43.74/43.95         (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.74/43.95          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 43.74/43.95               (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['45', '46'])).
% 43.74/43.95  thf('108', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (~ (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 43.74/43.95              (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['106', '107'])).
% 43.74/43.95  thf('109', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('110', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (~ (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 43.74/43.95              (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('demod', [status(thm)], ['108', '109'])).
% 43.74/43.95  thf('111', plain,
% 43.74/43.95      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 43.74/43.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.74/43.95  thf('112', plain,
% 43.74/43.95      ((((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1)))),
% 43.74/43.95      inference('eq_res', [status(thm)], ['25'])).
% 43.74/43.95  thf('113', plain,
% 43.74/43.95      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 43.74/43.95         (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 43.74/43.95      inference('demod', [status(thm)], ['6', '7'])).
% 43.74/43.95  thf('114', plain,
% 43.74/43.95      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 43.74/43.95         (((X24) = (k1_xboole_0))
% 43.74/43.95          | ((X25) = (k1_xboole_0))
% 43.74/43.95          | ((k2_zfmisc_1 @ X25 @ X24) != (k2_zfmisc_1 @ X26 @ X27))
% 43.74/43.95          | ((X25) = (X26)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 43.74/43.95  thf('115', plain,
% 43.74/43.95      (![X0 : $i, X1 : $i]:
% 43.74/43.95         (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k2_zfmisc_1 @ X1 @ X0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_A @ sk_C_1) = (X1))
% 43.74/43.95          | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['113', '114'])).
% 43.74/43.95  thf('116', plain,
% 43.74/43.95      ((((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A)))),
% 43.74/43.95      inference('eq_res', [status(thm)], ['115'])).
% 43.74/43.95  thf('117', plain,
% 43.74/43.95      ((((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A)))),
% 43.74/43.95      inference('eq_res', [status(thm)], ['115'])).
% 43.74/43.95  thf('118', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('119', plain,
% 43.74/43.95      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 43.74/43.95         (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 43.74/43.95      inference('demod', [status(thm)], ['6', '7'])).
% 43.74/43.95  thf('120', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 43.74/43.95          (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['118', '119'])).
% 43.74/43.95  thf('121', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('122', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 43.74/43.95          (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('demod', [status(thm)], ['120', '121'])).
% 43.74/43.95  thf('123', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ k1_xboole_0)
% 43.74/43.95           = (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['117', '122'])).
% 43.74/43.95  thf('124', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('125', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('126', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('127', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ k1_xboole_0)
% 43.74/43.95           = (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 43.74/43.95  thf('128', plain,
% 43.74/43.95      (((((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ k1_xboole_0)
% 43.74/43.95             = (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['127'])).
% 43.74/43.95  thf('129', plain,
% 43.74/43.95      (![X0 : $i, X1 : $i]:
% 43.74/43.95         (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k2_zfmisc_1 @ X1 @ X0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (X0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['23', '24'])).
% 43.74/43.95  thf('130', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['128', '129'])).
% 43.74/43.95  thf('131', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('132', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('133', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)
% 43.74/43.95           != (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('demod', [status(thm)], ['130', '131', '132'])).
% 43.74/43.95  thf('134', plain,
% 43.74/43.95      (((((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['133'])).
% 43.74/43.95  thf('135', plain,
% 43.74/43.95      (![X0 : $i, X2 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.74/43.95  thf('136', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ sk_B_1 @ sk_D))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['134', '135'])).
% 43.74/43.95  thf('137', plain,
% 43.74/43.95      ((((r1_xboole_0 @ sk_B_1 @ sk_D)
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['136'])).
% 43.74/43.95  thf('138', plain,
% 43.74/43.95      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ (k2_zfmisc_1 @ X22 @ X23))
% 43.74/43.95          | ~ (r1_xboole_0 @ X20 @ X22))),
% 43.74/43.95      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 43.74/43.95  thf('139', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          (((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ X1) @ 
% 43.74/43.95              (k2_zfmisc_1 @ sk_D @ X0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['137', '138'])).
% 43.74/43.95  thf('140', plain,
% 43.74/43.95      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 43.74/43.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.74/43.95  thf('141', plain,
% 43.74/43.95      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 43.74/43.95         ((k2_zfmisc_1 @ (k3_xboole_0 @ X16 @ X18) @ (k3_xboole_0 @ X17 @ X19))
% 43.74/43.95           = (k3_xboole_0 @ (k2_zfmisc_1 @ X16 @ X17) @ 
% 43.74/43.95              (k2_zfmisc_1 @ X18 @ X19)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 43.74/43.95  thf('142', plain,
% 43.74/43.95      (![X3 : $i, X5 : $i, X6 : $i]:
% 43.74/43.95         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 43.74/43.95          | ~ (r1_xboole_0 @ X3 @ X6))),
% 43.74/43.95      inference('cnf', [status(esa)], [t4_xboole_0])).
% 43.74/43.95  thf('143', plain,
% 43.74/43.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 43.74/43.95         (~ (r2_hidden @ X4 @ 
% 43.74/43.95             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 43.74/43.95          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['141', '142'])).
% 43.74/43.95  thf('144', plain,
% 43.74/43.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 43.74/43.95         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 43.74/43.95            = (k1_xboole_0))
% 43.74/43.95          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['140', '143'])).
% 43.74/43.95  thf('145', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          (((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95           | ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_B_1 @ sk_D) @ 
% 43.74/43.95               (k3_xboole_0 @ X1 @ X0)) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['139', '144'])).
% 43.74/43.95  thf('146', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          (((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 43.74/43.95             = (k1_xboole_0))
% 43.74/43.95           | ((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A))
% 43.74/43.95           | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95           | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['116', '145'])).
% 43.74/43.95  thf('147', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('148', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('149', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('150', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          (((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 43.74/43.95             = (k1_xboole_0))
% 43.74/43.95           | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95           | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95           | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 43.74/43.95  thf('151', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          (((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95           | ((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 43.74/43.95               = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['150'])).
% 43.74/43.95  thf('152', plain,
% 43.74/43.95      (![X0 : $i, X2 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.74/43.95  thf('153', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          (((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95           | ((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 43.74/43.95               = (k1_xboole_0))
% 43.74/43.95           | (r1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['151', '152'])).
% 43.74/43.95  thf('154', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          ((r1_xboole_0 @ k1_xboole_0 @ sk_C_1)
% 43.74/43.95           | ((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 43.74/43.95               = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['153'])).
% 43.74/43.95  thf('155', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['112', '154'])).
% 43.74/43.95  thf('156', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('157', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('demod', [status(thm)], ['155', '156'])).
% 43.74/43.95  thf('158', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 43.74/43.95  thf('159', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.74/43.95  thf('160', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['158', '159'])).
% 43.74/43.95  thf('161', plain,
% 43.74/43.95      (((((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['157', '160'])).
% 43.74/43.95  thf('162', plain,
% 43.74/43.95      (![X0 : $i, X2 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.74/43.95  thf('163', plain,
% 43.74/43.95      ((((r1_xboole_0 @ k1_xboole_0 @ sk_C_1)
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('clc', [status(thm)], ['161', '162'])).
% 43.74/43.95  thf('164', plain,
% 43.74/43.95      (![X0 : $i, X2 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.74/43.95  thf('165', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ k1_xboole_0 @ sk_C_1)
% 43.74/43.95         | (r1_xboole_0 @ sk_B_1 @ sk_D))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['163', '164'])).
% 43.74/43.95  thf('166', plain,
% 43.74/43.95      ((((r1_xboole_0 @ sk_B_1 @ sk_D) | (r1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['165'])).
% 43.74/43.95  thf('167', plain,
% 43.74/43.95      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ (k2_zfmisc_1 @ X22 @ X23))
% 43.74/43.95          | ~ (r1_xboole_0 @ X21 @ X23))),
% 43.74/43.95      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 43.74/43.95  thf('168', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          ((r1_xboole_0 @ k1_xboole_0 @ sk_C_1)
% 43.74/43.95           | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_B_1) @ 
% 43.74/43.95              (k2_zfmisc_1 @ X0 @ sk_D))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['166', '167'])).
% 43.74/43.95  thf('169', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (~ (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 43.74/43.95              (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('demod', [status(thm)], ['108', '109'])).
% 43.74/43.95  thf('170', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          ((r1_xboole_0 @ k1_xboole_0 @ sk_C_1)
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['168', '169'])).
% 43.74/43.95  thf('171', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['111', '170'])).
% 43.74/43.95  thf('172', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['158', '159'])).
% 43.74/43.95  thf('173', plain,
% 43.74/43.95      (((r1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['171', '172'])).
% 43.74/43.95  thf('174', plain,
% 43.74/43.95      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ (k2_zfmisc_1 @ X22 @ X23))
% 43.74/43.95          | ~ (r1_xboole_0 @ X20 @ X22))),
% 43.74/43.95      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 43.74/43.95  thf('175', plain,
% 43.74/43.95      ((![X0 : $i, X1 : $i]:
% 43.74/43.95          (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ 
% 43.74/43.95           (k2_zfmisc_1 @ sk_C_1 @ X0)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['173', '174'])).
% 43.74/43.95  thf('176', plain,
% 43.74/43.95      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('demod', [status(thm)], ['110', '175'])).
% 43.74/43.95  thf('177', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['68', '176'])).
% 43.74/43.95  thf('178', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['158', '159'])).
% 43.74/43.95  thf('179', plain, (((r1_tarski @ sk_B_1 @ sk_D))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['177', '178'])).
% 43.74/43.95  thf('180', plain,
% 43.74/43.95      (~ ((r1_tarski @ sk_A @ sk_C_1)) | ~ ((r1_tarski @ sk_B_1 @ sk_D))),
% 43.74/43.95      inference('split', [status(esa)], ['0'])).
% 43.74/43.95  thf('181', plain, (~ ((r1_tarski @ sk_A @ sk_C_1))),
% 43.74/43.95      inference('sat_resolution*', [status(thm)], ['179', '180'])).
% 43.74/43.95  thf('182', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_C_1)),
% 43.74/43.95      inference('simpl_trail', [status(thm)], ['67', '181'])).
% 43.74/43.95  thf('183', plain,
% 43.74/43.95      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 43.74/43.95      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.74/43.95  thf('184', plain,
% 43.74/43.95      ((((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A)))),
% 43.74/43.95      inference('eq_res', [status(thm)], ['115'])).
% 43.74/43.95  thf('185', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('186', plain,
% 43.74/43.95      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 43.74/43.95         (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 43.74/43.95      inference('demod', [status(thm)], ['6', '7'])).
% 43.74/43.95  thf('187', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 43.74/43.95          (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['185', '186'])).
% 43.74/43.95  thf('188', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('189', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ 
% 43.74/43.95          (k3_xboole_0 @ sk_B_1 @ sk_D)) = (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('demod', [status(thm)], ['187', '188'])).
% 43.74/43.95  thf('190', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ k1_xboole_0)
% 43.74/43.95           = (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup+', [status(thm)], ['184', '189'])).
% 43.74/43.95  thf('191', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('192', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('193', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('194', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ k1_xboole_0)
% 43.74/43.95           = (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('demod', [status(thm)], ['190', '191', '192', '193'])).
% 43.74/43.95  thf('195', plain,
% 43.74/43.95      (((((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k2_zfmisc_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_1) @ k1_xboole_0)
% 43.74/43.95             = (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['194'])).
% 43.74/43.95  thf('196', plain,
% 43.74/43.95      (![X0 : $i, X1 : $i]:
% 43.74/43.95         (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k2_zfmisc_1 @ X1 @ X0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (X0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95          | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['23', '24'])).
% 43.74/43.95  thf('197', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['195', '196'])).
% 43.74/43.95  thf('198', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('199', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('200', plain,
% 43.74/43.95      (((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)
% 43.74/43.95           != (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('demod', [status(thm)], ['197', '198', '199'])).
% 43.74/43.95  thf('201', plain,
% 43.74/43.95      (((((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['200'])).
% 43.74/43.95  thf('202', plain,
% 43.74/43.95      (![X0 : $i, X2 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 43.74/43.95  thf('203', plain,
% 43.74/43.95      (((((k1_xboole_0) != (k1_xboole_0))
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95         | (r1_xboole_0 @ sk_B_1 @ sk_D))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['201', '202'])).
% 43.74/43.95  thf('204', plain,
% 43.74/43.95      ((((r1_xboole_0 @ sk_B_1 @ sk_D)
% 43.74/43.95         | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify', [status(thm)], ['203'])).
% 43.74/43.95  thf('205', plain, (~ ((r1_tarski @ sk_A @ sk_C_1))),
% 43.74/43.95      inference('sat_resolution*', [status(thm)], ['179', '180'])).
% 43.74/43.95  thf('206', plain,
% 43.74/43.95      (((r1_xboole_0 @ sk_B_1 @ sk_D)
% 43.74/43.95        | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0)))),
% 43.74/43.95      inference('simpl_trail', [status(thm)], ['204', '205'])).
% 43.74/43.95  thf('207', plain,
% 43.74/43.95      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 43.74/43.95         ((r1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ (k2_zfmisc_1 @ X22 @ X23))
% 43.74/43.95          | ~ (r1_xboole_0 @ X21 @ X23))),
% 43.74/43.95      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 43.74/43.95  thf('208', plain,
% 43.74/43.95      (![X0 : $i, X1 : $i]:
% 43.74/43.95         (((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95          | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_B_1) @ 
% 43.74/43.95             (k2_zfmisc_1 @ X0 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['206', '207'])).
% 43.74/43.95  thf('209', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('210', plain,
% 43.74/43.95      (![X0 : $i]:
% 43.74/43.95         (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 43.74/43.95          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 43.74/43.95               (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['45', '46'])).
% 43.74/43.95  thf('211', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (~ (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 43.74/43.95              (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['209', '210'])).
% 43.74/43.95  thf('212', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('213', plain,
% 43.74/43.95      ((![X0 : $i]:
% 43.74/43.95          (~ (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 43.74/43.95              (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 43.74/43.95           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('demod', [status(thm)], ['211', '212'])).
% 43.74/43.95  thf('214', plain, (~ ((r1_tarski @ sk_A @ sk_C_1))),
% 43.74/43.95      inference('sat_resolution*', [status(thm)], ['179', '180'])).
% 43.74/43.95  thf('215', plain,
% 43.74/43.95      (![X0 : $i]:
% 43.74/43.95         (~ (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 43.74/43.95             (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 43.74/43.95          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)))),
% 43.74/43.95      inference('simpl_trail', [status(thm)], ['213', '214'])).
% 43.74/43.95  thf('216', plain,
% 43.74/43.95      (![X0 : $i]:
% 43.74/43.95         (((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))
% 43.74/43.95          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['208', '215'])).
% 43.74/43.95  thf('217', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) = (k1_xboole_0))
% 43.74/43.95        | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['183', '216'])).
% 43.74/43.95  thf('218', plain,
% 43.74/43.95      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 43.74/43.95  thf('219', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.74/43.95  thf('220', plain,
% 43.74/43.95      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0)))
% 43.74/43.95         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 43.74/43.95      inference('sup-', [status(thm)], ['218', '219'])).
% 43.74/43.95  thf('221', plain, (~ ((r1_tarski @ sk_A @ sk_C_1))),
% 43.74/43.95      inference('sat_resolution*', [status(thm)], ['179', '180'])).
% 43.74/43.95  thf('222', plain, (((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) != (k1_xboole_0))),
% 43.74/43.95      inference('simpl_trail', [status(thm)], ['220', '221'])).
% 43.74/43.95  thf('223', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))),
% 43.74/43.95      inference('simplify_reflect-', [status(thm)], ['217', '222'])).
% 43.74/43.95  thf('224', plain,
% 43.74/43.95      (![X11 : $i, X12 : $i]:
% 43.74/43.95         ((k4_xboole_0 @ X11 @ X12)
% 43.74/43.95           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 43.74/43.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 43.74/43.95  thf('225', plain,
% 43.74/43.95      (((k4_xboole_0 @ k1_xboole_0 @ sk_C_1)
% 43.74/43.95         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 43.74/43.95      inference('sup+', [status(thm)], ['223', '224'])).
% 43.74/43.95  thf('226', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 43.74/43.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 43.74/43.95  thf('227', plain, (((k4_xboole_0 @ k1_xboole_0 @ sk_C_1) = (k1_xboole_0))),
% 43.74/43.95      inference('demod', [status(thm)], ['225', '226'])).
% 43.74/43.95  thf('228', plain,
% 43.74/43.95      (![X8 : $i, X9 : $i]:
% 43.74/43.95         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 43.74/43.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 43.74/43.95  thf('229', plain,
% 43.74/43.95      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ sk_C_1))),
% 43.74/43.95      inference('sup-', [status(thm)], ['227', '228'])).
% 43.74/43.95  thf('230', plain, ((r1_tarski @ k1_xboole_0 @ sk_C_1)),
% 43.74/43.95      inference('simplify', [status(thm)], ['229'])).
% 43.74/43.95  thf('231', plain, ($false), inference('demod', [status(thm)], ['182', '230'])).
% 43.74/43.95  
% 43.74/43.95  % SZS output end Refutation
% 43.74/43.95  
% 43.74/43.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
