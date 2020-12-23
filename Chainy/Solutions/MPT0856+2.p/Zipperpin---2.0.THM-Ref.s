%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0856+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C31hXlW3zZ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   33 (  44 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 ( 313 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_72_type,type,(
    sk_B_72: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t12_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k1_tarski @ B @ C ) ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k1_tarski @ B @ C ) ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( r2_hidden @ ( k2_mcart_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_mcart_1])).

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_72 @ sk_C_93 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A @ B ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A @ C ) ) ) ) )).

thf('3',plain,(
    ! [X3850: $i,X3851: $i,X3852: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X3850 @ X3851 ) )
      | ~ ( r2_hidden @ ( X3850 @ ( k2_zfmisc_1 @ ( X3851 @ X3852 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ ( k1_tarski @ sk_B_72 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X1021: $i,X1023: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1021 @ X1023 ) )
      | ~ ( r2_hidden @ ( X1021 @ X1023 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_mcart_1 @ sk_A_14 ) @ ( k1_tarski @ sk_B_72 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
     => ( A = B ) ) )).

thf('7',plain,(
    ! [X1263: $i,X1264: $i] :
      ( ( X1264 = X1263 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1264 @ ( k1_tarski @ X1263 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_zfmisc_1])).

thf('8',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = sk_B_72 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( sk_B_72 != sk_B_72 )
   <= ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = sk_B_72 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) )
    | ( ( k1_mcart_1 @ sk_A_14 )
     != sk_B_72 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference('sat_resolution*',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_72 @ sk_C_93 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X3850: $i,X3851: $i,X3852: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X3850 @ X3852 ) )
      | ~ ( r2_hidden @ ( X3850 @ ( k2_zfmisc_1 @ ( X3851 @ X3852 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('17',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['14','17'])).

%------------------------------------------------------------------------------
