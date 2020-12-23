%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j0tT4dhPtd

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:33 EST 2020

% Result     : Theorem 6.95s
% Output     : Refutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 772 expanded)
%              Number of leaves         :   33 ( 265 expanded)
%              Depth                    :   28
%              Number of atoms          :  997 (5183 expanded)
%              Number of equality atoms :   80 ( 253 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X16 @ X17 ) @ ( sk_D @ X16 @ X17 ) ) @ X16 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X16 @ X17 ) @ ( sk_C_2 @ X16 @ X17 ) ) @ X17 )
      | ( X16
        = ( k4_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('23',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('29',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('36',plain,(
    ! [X25: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X29 @ X28 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X28 ) @ ( k4_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

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

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('52',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('53',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('54',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X27 @ X26 ) ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['50','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('73',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','77'])).

thf('79',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','77'])).

thf('80',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['48','78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('83',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X25: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X25 ) )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','91'])).

thf('93',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','77'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('97',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('101',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('102',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('105',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['97'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('110',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['97'])).

thf('116',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['99','116'])).

thf('118',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('121',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    $false ),
    inference(simplify,[status(thm)],['121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j0tT4dhPtd
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.95/7.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.95/7.14  % Solved by: fo/fo7.sh
% 6.95/7.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.95/7.14  % done 6956 iterations in 6.688s
% 6.95/7.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.95/7.14  % SZS output start Refutation
% 6.95/7.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.95/7.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.95/7.14  thf(sk_A_type, type, sk_A: $i).
% 6.95/7.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.95/7.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.95/7.14  thf(sk_B_type, type, sk_B: $i > $i).
% 6.95/7.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.95/7.14  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 6.95/7.14  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.95/7.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.95/7.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.95/7.14  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 6.95/7.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.95/7.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.95/7.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.95/7.14  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.95/7.14  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 6.95/7.14  thf(dt_k5_relat_1, axiom,
% 6.95/7.14    (![A:$i,B:$i]:
% 6.95/7.14     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 6.95/7.14       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 6.95/7.14  thf('0', plain,
% 6.95/7.14      (![X22 : $i, X23 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X22)
% 6.95/7.14          | ~ (v1_relat_1 @ X23)
% 6.95/7.14          | (v1_relat_1 @ (k5_relat_1 @ X22 @ X23)))),
% 6.95/7.14      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 6.95/7.14  thf(t60_relat_1, axiom,
% 6.95/7.14    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 6.95/7.14     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.95/7.14  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.95/7.14      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.95/7.14  thf(l13_xboole_0, axiom,
% 6.95/7.14    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.95/7.14  thf('2', plain,
% 6.95/7.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.95/7.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.95/7.14  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.95/7.14      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.95/7.14  thf('4', plain,
% 6.95/7.14      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.95/7.14      inference('sup+', [status(thm)], ['2', '3'])).
% 6.95/7.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.95/7.14  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('6', plain,
% 6.95/7.14      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.95/7.14      inference('sup+', [status(thm)], ['4', '5'])).
% 6.95/7.14  thf(t3_xboole_0, axiom,
% 6.95/7.14    (![A:$i,B:$i]:
% 6.95/7.14     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 6.95/7.14            ( r1_xboole_0 @ A @ B ) ) ) & 
% 6.95/7.14       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 6.95/7.14            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 6.95/7.14  thf('7', plain,
% 6.95/7.14      (![X4 : $i, X5 : $i]:
% 6.95/7.14         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 6.95/7.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.95/7.14  thf(d1_xboole_0, axiom,
% 6.95/7.14    (![A:$i]:
% 6.95/7.14     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.95/7.14  thf('8', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.95/7.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.95/7.14  thf('9', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['7', '8'])).
% 6.95/7.14  thf('10', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]:
% 6.95/7.14         (~ (v1_xboole_0 @ X0) | (r1_xboole_0 @ X1 @ (k2_relat_1 @ X0)))),
% 6.95/7.14      inference('sup-', [status(thm)], ['6', '9'])).
% 6.95/7.14  thf('11', plain,
% 6.95/7.14      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.95/7.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.95/7.14  thf(t4_xboole_0, axiom,
% 6.95/7.14    (![A:$i,B:$i]:
% 6.95/7.14     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 6.95/7.14            ( r1_xboole_0 @ A @ B ) ) ) & 
% 6.95/7.14       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 6.95/7.14            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 6.95/7.14  thf('12', plain,
% 6.95/7.14      (![X8 : $i, X10 : $i, X11 : $i]:
% 6.95/7.14         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 6.95/7.14          | ~ (r1_xboole_0 @ X8 @ X11))),
% 6.95/7.14      inference('cnf', [status(esa)], [t4_xboole_0])).
% 6.95/7.14  thf('13', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]:
% 6.95/7.14         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['11', '12'])).
% 6.95/7.14  thf('14', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]:
% 6.95/7.14         (~ (v1_xboole_0 @ X0)
% 6.95/7.14          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 6.95/7.14      inference('sup-', [status(thm)], ['10', '13'])).
% 6.95/7.14  thf(cc1_relat_1, axiom,
% 6.95/7.14    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 6.95/7.14  thf('15', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 6.95/7.14      inference('cnf', [status(esa)], [cc1_relat_1])).
% 6.95/7.14  thf(d7_relat_1, axiom,
% 6.95/7.14    (![A:$i]:
% 6.95/7.14     ( ( v1_relat_1 @ A ) =>
% 6.95/7.14       ( ![B:$i]:
% 6.95/7.14         ( ( v1_relat_1 @ B ) =>
% 6.95/7.14           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 6.95/7.14             ( ![C:$i,D:$i]:
% 6.95/7.14               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 6.95/7.14                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 6.95/7.14  thf('16', plain,
% 6.95/7.14      (![X16 : $i, X17 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X16)
% 6.95/7.14          | (r2_hidden @ 
% 6.95/7.14             (k4_tarski @ (sk_C_2 @ X16 @ X17) @ (sk_D @ X16 @ X17)) @ X16)
% 6.95/7.14          | (r2_hidden @ 
% 6.95/7.14             (k4_tarski @ (sk_D @ X16 @ X17) @ (sk_C_2 @ X16 @ X17)) @ X17)
% 6.95/7.14          | ((X16) = (k4_relat_1 @ X17))
% 6.95/7.14          | ~ (v1_relat_1 @ X17))),
% 6.95/7.14      inference('cnf', [status(esa)], [d7_relat_1])).
% 6.95/7.14  thf('17', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.95/7.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.95/7.14  thf('18', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((X1) = (k4_relat_1 @ X0))
% 6.95/7.14          | (r2_hidden @ (k4_tarski @ (sk_C_2 @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ 
% 6.95/7.14             X1)
% 6.95/7.14          | ~ (v1_relat_1 @ X1)
% 6.95/7.14          | ~ (v1_xboole_0 @ X0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['16', '17'])).
% 6.95/7.14  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('20', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['7', '8'])).
% 6.95/7.14  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 6.95/7.14      inference('sup-', [status(thm)], ['19', '20'])).
% 6.95/7.14  thf('22', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]:
% 6.95/7.14         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['11', '12'])).
% 6.95/7.14  thf('23', plain,
% 6.95/7.14      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['21', '22'])).
% 6.95/7.14  thf('24', plain,
% 6.95/7.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.95/7.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.95/7.14  thf('25', plain,
% 6.95/7.14      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['23', '24'])).
% 6.95/7.14  thf('26', plain,
% 6.95/7.14      (![X8 : $i, X10 : $i, X11 : $i]:
% 6.95/7.14         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 6.95/7.14          | ~ (r1_xboole_0 @ X8 @ X11))),
% 6.95/7.14      inference('cnf', [status(esa)], [t4_xboole_0])).
% 6.95/7.14  thf('27', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]:
% 6.95/7.14         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['25', '26'])).
% 6.95/7.14  thf('28', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 6.95/7.14      inference('sup-', [status(thm)], ['19', '20'])).
% 6.95/7.14  thf('29', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 6.95/7.14      inference('demod', [status(thm)], ['27', '28'])).
% 6.95/7.14  thf('30', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_xboole_0 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ k1_xboole_0)
% 6.95/7.14          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 6.95/7.14          | ~ (v1_relat_1 @ X0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['18', '29'])).
% 6.95/7.14  thf('31', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 6.95/7.14          | ~ (v1_xboole_0 @ X0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['15', '30'])).
% 6.95/7.14  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('33', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 6.95/7.14          | ~ (v1_xboole_0 @ X0))),
% 6.95/7.14      inference('demod', [status(thm)], ['31', '32'])).
% 6.95/7.14  thf('34', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 6.95/7.14      inference('cnf', [status(esa)], [cc1_relat_1])).
% 6.95/7.14  thf('35', plain,
% 6.95/7.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k4_relat_1 @ X0)))),
% 6.95/7.14      inference('clc', [status(thm)], ['33', '34'])).
% 6.95/7.14  thf(involutiveness_k4_relat_1, axiom,
% 6.95/7.14    (![A:$i]:
% 6.95/7.14     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 6.95/7.14  thf('36', plain,
% 6.95/7.14      (![X25 : $i]:
% 6.95/7.14         (((k4_relat_1 @ (k4_relat_1 @ X25)) = (X25)) | ~ (v1_relat_1 @ X25))),
% 6.95/7.14      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 6.95/7.14  thf('37', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (((k4_relat_1 @ k1_xboole_0) = (X0))
% 6.95/7.14          | ~ (v1_xboole_0 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0))),
% 6.95/7.14      inference('sup+', [status(thm)], ['35', '36'])).
% 6.95/7.14  thf('38', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 6.95/7.14      inference('cnf', [status(esa)], [cc1_relat_1])).
% 6.95/7.14  thf('39', plain,
% 6.95/7.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ k1_xboole_0) = (X0)))),
% 6.95/7.14      inference('clc', [status(thm)], ['37', '38'])).
% 6.95/7.14  thf('40', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]:
% 6.95/7.14         (~ (v1_xboole_0 @ X0)
% 6.95/7.14          | ((k4_relat_1 @ k1_xboole_0)
% 6.95/7.14              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 6.95/7.14      inference('sup-', [status(thm)], ['14', '39'])).
% 6.95/7.14  thf('41', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (((k4_relat_1 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 6.95/7.14          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.95/7.14      inference('sup+', [status(thm)], ['1', '40'])).
% 6.95/7.14  thf('42', plain,
% 6.95/7.14      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['23', '24'])).
% 6.95/7.14  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('44', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.95/7.14      inference('demod', [status(thm)], ['41', '42', '43'])).
% 6.95/7.14  thf('45', plain,
% 6.95/7.14      (![X25 : $i]:
% 6.95/7.14         (((k4_relat_1 @ (k4_relat_1 @ X25)) = (X25)) | ~ (v1_relat_1 @ X25))),
% 6.95/7.14      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 6.95/7.14  thf(t54_relat_1, axiom,
% 6.95/7.14    (![A:$i]:
% 6.95/7.14     ( ( v1_relat_1 @ A ) =>
% 6.95/7.14       ( ![B:$i]:
% 6.95/7.14         ( ( v1_relat_1 @ B ) =>
% 6.95/7.14           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 6.95/7.14             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 6.95/7.14  thf('46', plain,
% 6.95/7.14      (![X28 : $i, X29 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X28)
% 6.95/7.14          | ((k4_relat_1 @ (k5_relat_1 @ X29 @ X28))
% 6.95/7.14              = (k5_relat_1 @ (k4_relat_1 @ X28) @ (k4_relat_1 @ X29)))
% 6.95/7.14          | ~ (v1_relat_1 @ X29))),
% 6.95/7.14      inference('cnf', [status(esa)], [t54_relat_1])).
% 6.95/7.14  thf('47', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]:
% 6.95/7.14         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 6.95/7.14            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 6.95/7.14          | ~ (v1_relat_1 @ X1))),
% 6.95/7.14      inference('sup+', [status(thm)], ['45', '46'])).
% 6.95/7.14  thf('48', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ k1_xboole_0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ k1_xboole_0)
% 6.95/7.14          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 6.95/7.14              = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0)))),
% 6.95/7.14      inference('sup-', [status(thm)], ['44', '47'])).
% 6.95/7.14  thf(t62_relat_1, conjecture,
% 6.95/7.14    (![A:$i]:
% 6.95/7.14     ( ( v1_relat_1 @ A ) =>
% 6.95/7.14       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 6.95/7.14         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 6.95/7.14  thf(zf_stmt_0, negated_conjecture,
% 6.95/7.14    (~( ![A:$i]:
% 6.95/7.14        ( ( v1_relat_1 @ A ) =>
% 6.95/7.14          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 6.95/7.14            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 6.95/7.14    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 6.95/7.14  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 6.95/7.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.95/7.14  thf('50', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 6.95/7.14      inference('cnf', [status(esa)], [cc1_relat_1])).
% 6.95/7.14  thf('51', plain,
% 6.95/7.14      (![X22 : $i, X23 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X22)
% 6.95/7.14          | ~ (v1_relat_1 @ X23)
% 6.95/7.14          | (v1_relat_1 @ (k5_relat_1 @ X22 @ X23)))),
% 6.95/7.14      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 6.95/7.14  thf('52', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 6.95/7.14      inference('cnf', [status(esa)], [cc1_relat_1])).
% 6.95/7.14  thf('53', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.95/7.14      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.95/7.14  thf(t45_relat_1, axiom,
% 6.95/7.14    (![A:$i]:
% 6.95/7.14     ( ( v1_relat_1 @ A ) =>
% 6.95/7.14       ( ![B:$i]:
% 6.95/7.14         ( ( v1_relat_1 @ B ) =>
% 6.95/7.14           ( r1_tarski @
% 6.95/7.14             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 6.95/7.14  thf('54', plain,
% 6.95/7.14      (![X26 : $i, X27 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X26)
% 6.95/7.14          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X27 @ X26)) @ 
% 6.95/7.14             (k2_relat_1 @ X26))
% 6.95/7.14          | ~ (v1_relat_1 @ X27))),
% 6.95/7.14      inference('cnf', [status(esa)], [t45_relat_1])).
% 6.95/7.14  thf('55', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 6.95/7.14           k1_xboole_0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ k1_xboole_0))),
% 6.95/7.14      inference('sup+', [status(thm)], ['53', '54'])).
% 6.95/7.14  thf('56', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 6.95/7.14             k1_xboole_0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['52', '55'])).
% 6.95/7.14  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('58', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 6.95/7.14             k1_xboole_0))),
% 6.95/7.14      inference('demod', [status(thm)], ['56', '57'])).
% 6.95/7.14  thf(t28_xboole_1, axiom,
% 6.95/7.14    (![A:$i,B:$i]:
% 6.95/7.14     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.95/7.14  thf('59', plain,
% 6.95/7.14      (![X13 : $i, X14 : $i]:
% 6.95/7.14         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 6.95/7.14      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.95/7.14  thf('60', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 6.95/7.14              k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 6.95/7.14      inference('sup-', [status(thm)], ['58', '59'])).
% 6.95/7.14  thf('61', plain,
% 6.95/7.14      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['23', '24'])).
% 6.95/7.14  thf('62', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 6.95/7.14      inference('demod', [status(thm)], ['60', '61'])).
% 6.95/7.14  thf(fc9_relat_1, axiom,
% 6.95/7.14    (![A:$i]:
% 6.95/7.14     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 6.95/7.14       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 6.95/7.14  thf('63', plain,
% 6.95/7.14      (![X24 : $i]:
% 6.95/7.14         (~ (v1_xboole_0 @ (k2_relat_1 @ X24))
% 6.95/7.14          | ~ (v1_relat_1 @ X24)
% 6.95/7.14          | (v1_xboole_0 @ X24))),
% 6.95/7.14      inference('cnf', [status(esa)], [fc9_relat_1])).
% 6.95/7.14  thf('64', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 6.95/7.14          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 6.95/7.14      inference('sup-', [status(thm)], ['62', '63'])).
% 6.95/7.14  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('66', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 6.95/7.14          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 6.95/7.14      inference('demod', [status(thm)], ['64', '65'])).
% 6.95/7.14  thf('67', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ k1_xboole_0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 6.95/7.14          | ~ (v1_relat_1 @ X0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['51', '66'])).
% 6.95/7.14  thf('68', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ k1_xboole_0))),
% 6.95/7.14      inference('simplify', [status(thm)], ['67'])).
% 6.95/7.14  thf('69', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 6.95/7.14      inference('sup-', [status(thm)], ['50', '68'])).
% 6.95/7.14  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('71', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 6.95/7.14      inference('demod', [status(thm)], ['69', '70'])).
% 6.95/7.14  thf('72', plain,
% 6.95/7.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k4_relat_1 @ X0)))),
% 6.95/7.14      inference('clc', [status(thm)], ['33', '34'])).
% 6.95/7.14  thf(dt_k4_relat_1, axiom,
% 6.95/7.14    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 6.95/7.14  thf('73', plain,
% 6.95/7.14      (![X21 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X21)) | ~ (v1_relat_1 @ X21))),
% 6.95/7.14      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 6.95/7.14  thf('74', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         ((v1_relat_1 @ k1_xboole_0)
% 6.95/7.14          | ~ (v1_xboole_0 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0))),
% 6.95/7.14      inference('sup+', [status(thm)], ['72', '73'])).
% 6.95/7.14  thf('75', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 6.95/7.14      inference('cnf', [status(esa)], [cc1_relat_1])).
% 6.95/7.14  thf('76', plain,
% 6.95/7.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 6.95/7.14      inference('clc', [status(thm)], ['74', '75'])).
% 6.95/7.14  thf('77', plain,
% 6.95/7.14      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['71', '76'])).
% 6.95/7.14  thf('78', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.95/7.14      inference('sup-', [status(thm)], ['49', '77'])).
% 6.95/7.14  thf('79', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.95/7.14      inference('sup-', [status(thm)], ['49', '77'])).
% 6.95/7.14  thf('80', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.95/7.14      inference('demod', [status(thm)], ['41', '42', '43'])).
% 6.95/7.14  thf('81', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 6.95/7.14              = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0)))),
% 6.95/7.14      inference('demod', [status(thm)], ['48', '78', '79', '80'])).
% 6.95/7.14  thf('82', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 6.95/7.14      inference('demod', [status(thm)], ['69', '70'])).
% 6.95/7.14  thf('83', plain,
% 6.95/7.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.95/7.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.95/7.14  thf('84', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 6.95/7.14      inference('sup-', [status(thm)], ['82', '83'])).
% 6.95/7.14  thf('85', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 6.95/7.14      inference('sup+', [status(thm)], ['81', '84'])).
% 6.95/7.14  thf('86', plain,
% 6.95/7.14      (![X21 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X21)) | ~ (v1_relat_1 @ X21))),
% 6.95/7.14      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 6.95/7.14  thf('87', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 6.95/7.14      inference('clc', [status(thm)], ['85', '86'])).
% 6.95/7.14  thf('88', plain,
% 6.95/7.14      (![X25 : $i]:
% 6.95/7.14         (((k4_relat_1 @ (k4_relat_1 @ X25)) = (X25)) | ~ (v1_relat_1 @ X25))),
% 6.95/7.14      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 6.95/7.14  thf('89', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 6.95/7.14      inference('sup+', [status(thm)], ['87', '88'])).
% 6.95/7.14  thf('90', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.95/7.14      inference('demod', [status(thm)], ['41', '42', '43'])).
% 6.95/7.14  thf('91', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 6.95/7.14      inference('demod', [status(thm)], ['89', '90'])).
% 6.95/7.14  thf('92', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ k1_xboole_0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 6.95/7.14      inference('sup-', [status(thm)], ['0', '91'])).
% 6.95/7.14  thf('93', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.95/7.14      inference('sup-', [status(thm)], ['49', '77'])).
% 6.95/7.14  thf('94', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0)
% 6.95/7.14          | ~ (v1_relat_1 @ X0)
% 6.95/7.14          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 6.95/7.14      inference('demod', [status(thm)], ['92', '93'])).
% 6.95/7.14  thf('95', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 6.95/7.14          | ~ (v1_relat_1 @ X0))),
% 6.95/7.14      inference('simplify', [status(thm)], ['94'])).
% 6.95/7.14  thf('96', plain,
% 6.95/7.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.95/7.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.95/7.14  thf('97', plain,
% 6.95/7.14      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 6.95/7.14        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 6.95/7.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.95/7.14  thf('98', plain,
% 6.95/7.14      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 6.95/7.14         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 6.95/7.14      inference('split', [status(esa)], ['97'])).
% 6.95/7.14  thf('99', plain,
% 6.95/7.14      ((![X0 : $i]:
% 6.95/7.14          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 6.95/7.14         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 6.95/7.14      inference('sup-', [status(thm)], ['96', '98'])).
% 6.95/7.14  thf('100', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 6.95/7.14      inference('demod', [status(thm)], ['69', '70'])).
% 6.95/7.14  thf('101', plain,
% 6.95/7.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.95/7.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.95/7.14  thf('102', plain,
% 6.95/7.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.95/7.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.95/7.14  thf('103', plain,
% 6.95/7.14      (![X0 : $i, X1 : $i]:
% 6.95/7.14         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 6.95/7.14      inference('sup+', [status(thm)], ['101', '102'])).
% 6.95/7.14  thf('104', plain,
% 6.95/7.14      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.95/7.14      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.95/7.14  thf('105', plain,
% 6.95/7.14      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 6.95/7.14         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 6.95/7.14      inference('split', [status(esa)], ['97'])).
% 6.95/7.14  thf('106', plain,
% 6.95/7.14      ((![X0 : $i]:
% 6.95/7.14          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 6.95/7.14         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 6.95/7.14      inference('sup-', [status(thm)], ['104', '105'])).
% 6.95/7.14  thf('107', plain,
% 6.95/7.14      ((![X0 : $i, X1 : $i]:
% 6.95/7.14          (((X0) != (k1_xboole_0))
% 6.95/7.14           | ~ (v1_xboole_0 @ X0)
% 6.95/7.14           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 6.95/7.14           | ~ (v1_xboole_0 @ X1)))
% 6.95/7.14         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 6.95/7.14      inference('sup-', [status(thm)], ['103', '106'])).
% 6.95/7.14  thf('108', plain,
% 6.95/7.14      ((![X1 : $i]:
% 6.95/7.14          (~ (v1_xboole_0 @ X1)
% 6.95/7.14           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 6.95/7.14           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 6.95/7.14         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 6.95/7.14      inference('simplify', [status(thm)], ['107'])).
% 6.95/7.14  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('110', plain,
% 6.95/7.14      ((![X1 : $i]:
% 6.95/7.14          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 6.95/7.14         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 6.95/7.14      inference('simplify_reflect+', [status(thm)], ['108', '109'])).
% 6.95/7.14  thf('111', plain,
% 6.95/7.14      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 6.95/7.14         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 6.95/7.14      inference('sup-', [status(thm)], ['100', '110'])).
% 6.95/7.14  thf('112', plain, ((v1_relat_1 @ sk_A)),
% 6.95/7.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.95/7.14  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('114', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 6.95/7.14      inference('demod', [status(thm)], ['111', '112', '113'])).
% 6.95/7.14  thf('115', plain,
% 6.95/7.14      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 6.95/7.14       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 6.95/7.14      inference('split', [status(esa)], ['97'])).
% 6.95/7.14  thf('116', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 6.95/7.14      inference('sat_resolution*', [status(thm)], ['114', '115'])).
% 6.95/7.14  thf('117', plain,
% 6.95/7.14      (![X0 : $i]:
% 6.95/7.14         (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.95/7.14      inference('simpl_trail', [status(thm)], ['99', '116'])).
% 6.95/7.14  thf('118', plain,
% 6.95/7.14      ((((k1_xboole_0) != (k1_xboole_0))
% 6.95/7.14        | ~ (v1_relat_1 @ sk_A)
% 6.95/7.14        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.95/7.14      inference('sup-', [status(thm)], ['95', '117'])).
% 6.95/7.14  thf('119', plain, ((v1_relat_1 @ sk_A)),
% 6.95/7.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.95/7.14  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.95/7.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.95/7.14  thf('121', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 6.95/7.14      inference('demod', [status(thm)], ['118', '119', '120'])).
% 6.95/7.14  thf('122', plain, ($false), inference('simplify', [status(thm)], ['121'])).
% 6.95/7.14  
% 6.95/7.14  % SZS output end Refutation
% 6.95/7.14  
% 6.95/7.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
