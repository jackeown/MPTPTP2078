%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0337+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pDRST1pn4X

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  33 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :  190 ( 254 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t151_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ! [C: $i,D: $i] :
          ( ( ( r2_hidden @ C @ A )
            & ( r2_hidden @ D @ B ) )
         => ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ B ) )
           => ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X2 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X2 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ sk_A )
      | ~ ( r2_hidden @ X5 @ sk_B )
      | ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) )
      | ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X2 ) @ X3 )
      | ~ ( r1_xboole_0 @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( sk_C @ X0 @ sk_B ) )
      | ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C @ X0 @ sk_B ) @ ( k3_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X2 ) @ X3 )
      | ~ ( r1_xboole_0 @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('12',plain,
    ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_A ) )
    | ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('15',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).


%------------------------------------------------------------------------------
