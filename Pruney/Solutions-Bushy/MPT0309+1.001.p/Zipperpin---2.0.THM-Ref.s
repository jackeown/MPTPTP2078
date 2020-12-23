%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0309+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s3UZ9ZNNpE

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  266 ( 351 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t121_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ C @ D ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ A @ D ) ) @ ( k2_zfmisc_1 @ B @ C ) ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ C @ D ) )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ A @ D ) ) @ ( k2_zfmisc_1 @ B @ C ) ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) )
 != ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('6',plain,(
    ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('11',plain,(
    ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) )
 != ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['6','9','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).


%------------------------------------------------------------------------------
