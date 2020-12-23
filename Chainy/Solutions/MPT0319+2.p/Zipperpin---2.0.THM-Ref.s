%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0319+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sbPbbgKlpy

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 31.09s
% Output     : Refutation 31.09s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  291 ( 516 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_13_type,type,(
    sk_D_13: $i )).

thf(sk_C_13_type,type,(
    sk_C_13: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1159: $i,X1160: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1159 @ ( k1_tarski @ X1160 ) ) )
      | ( X1159 = X1160 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ ( A @ B ) )
        | ( r1_xboole_0 @ ( C @ D ) ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( A @ C ) @ ( k2_zfmisc_1 @ ( B @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X1135: $i,X1136: $i,X1137: $i,X1138: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( X1135 @ X1136 ) @ ( k2_zfmisc_1 @ ( X1137 @ X1138 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X1136 @ X1138 ) ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( X3 @ ( k1_tarski @ X1 ) ) @ ( k2_zfmisc_1 @ ( X2 @ ( k1_tarski @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t131_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( A != B )
     => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B @ D ) ) ) )
        & ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ ( D @ ( k1_tarski @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( A != B )
       => ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B @ D ) ) ) )
          & ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ ( D @ ( k1_tarski @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_zfmisc_1])).

thf('3',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_D_13 ) ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_D_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_D_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_D_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ ( A @ B ) )
     => ( r1_xboole_0 @ ( k1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X1021: $i,X1022: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1021 @ X1022 ) )
      | ( r2_hidden @ ( X1021 @ X1022 ) ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('6',plain,(
    ! [X1135: $i,X1136: $i,X1137: $i,X1138: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( X1135 @ X1136 ) @ ( k2_zfmisc_1 @ ( X1137 @ X1138 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X1135 @ X1137 ) ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ ( X0 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_D_13 ) ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_D_13 ) ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_D_13 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1159: $i,X1160: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1159 @ ( k1_tarski @ X1160 ) ) )
      | ( X1159 = X1160 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A @ B ) )
        & ( r2_hidden @ ( A @ B ) ) ) )).

thf('11',plain,(
    ! [X1019: $i,X1020: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X1019 @ X1020 ) )
      | ~ ( r2_hidden @ ( X1019 @ X1020 ) ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A_2 = sk_B_2 )
   <= ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_D_13 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_A_2 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_D_13 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_D_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A_2 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_D_13 ) ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_D_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_C_13 @ ( k1_tarski @ sk_A_2 ) ) @ ( k2_zfmisc_1 @ ( sk_D_13 @ ( k1_tarski @ sk_B_2 ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['4','17'])).

thf('19',plain,(
    sk_A_2 = sk_B_2 ),
    inference('sup-',[status(thm)],['2','18'])).

thf('20',plain,(
    sk_A_2 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
