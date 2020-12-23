%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0928+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PQZpt0zMAO

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:44 EST 2020

% Result     : Theorem 5.33s
% Output     : Refutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  245 ( 441 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t88_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_tarski @ E @ F )
        & ( r1_tarski @ G @ H ) )
     => ( r1_tarski @ ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D )
          & ( r1_tarski @ E @ F )
          & ( r1_tarski @ G @ H ) )
       => ( r1_tarski @ ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_mcart_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G ) @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_G @ sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tarski @ sk_E @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t77_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_tarski @ E @ F ) )
     => ( r1_tarski @ ( k3_zfmisc_1 @ A @ C @ E ) @ ( k3_zfmisc_1 @ B @ D @ F ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k3_zfmisc_1 @ X10 @ X8 @ X12 ) @ ( k3_zfmisc_1 @ X11 @ X9 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t77_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_zfmisc_1 @ X3 @ sk_C @ X2 ) @ ( k3_zfmisc_1 @ X1 @ sk_D @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X3 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k3_zfmisc_1 @ X1 @ sk_C @ sk_E ) @ ( k3_zfmisc_1 @ X0 @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_zfmisc_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t119_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_C @ sk_E ) @ X1 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_B @ sk_D @ sk_F ) @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ X1 ) @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G ) @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).


%------------------------------------------------------------------------------
