%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0892+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GYFt6RPm6a

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   46 (  70 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  352 ( 697 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t52_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ~ ( r1_xboole_0 @ A @ D )
        & ~ ( r1_xboole_0 @ B @ E )
        & ~ ( r1_xboole_0 @ C @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ A @ B @ C ) @ ( k3_zfmisc_1 @ D @ E @ F ) )
       => ( ~ ( r1_xboole_0 @ A @ D )
          & ~ ( r1_xboole_0 @ B @ E )
          & ~ ( r1_xboole_0 @ C @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_mcart_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_D )
    | ( r1_xboole_0 @ sk_B @ sk_E )
    | ( r1_xboole_0 @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_F )
   <= ( r1_xboole_0 @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['3'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('6',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) )
   <= ( r1_xboole_0 @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X2 @ sk_F ) )
   <= ( r1_xboole_0 @ sk_C @ sk_F ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_D )
   <= ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('10',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_D @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('12',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) @ X2 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ X1 @ X3 ) @ ( k3_zfmisc_1 @ sk_D @ X0 @ X2 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_E )
   <= ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('20',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_E ) )
   <= ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('22',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_E ) @ X2 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( r1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ sk_B @ X3 ) @ ( k3_zfmisc_1 @ X0 @ sk_E @ X2 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_F )
    | ( r1_xboole_0 @ sk_B @ sk_E )
    | ( r1_xboole_0 @ sk_A @ sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,(
    r1_xboole_0 @ sk_C @ sk_F ),
    inference('sat_resolution*',[status(thm)],['17','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X2 @ sk_F ) ) ),
    inference(simpl_trail,[status(thm)],['7','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ sk_C ) @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_F ) ) ),
    inference('sup+',[status(thm)],['1','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).


%------------------------------------------------------------------------------
