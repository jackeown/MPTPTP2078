%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M8xVuU2QUk

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:26 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 389 expanded)
%              Number of leaves         :   26 ( 138 expanded)
%              Depth                    :   24
%              Number of atoms          :  843 (3145 expanded)
%              Number of equality atoms :   66 ( 244 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_D_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('13',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ( r1_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['4','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['29','42'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('58',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','62','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','62','65'])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('73',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70','77','78'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('80',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('85',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','89'])).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('92',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M8xVuU2QUk
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.16/2.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.16/2.34  % Solved by: fo/fo7.sh
% 2.16/2.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.16/2.34  % done 3844 iterations in 1.875s
% 2.16/2.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.16/2.34  % SZS output start Refutation
% 2.16/2.34  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.16/2.34  thf(sk_A_type, type, sk_A: $i).
% 2.16/2.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.16/2.34  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.16/2.34  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.16/2.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.16/2.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.16/2.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.16/2.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.16/2.34  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.16/2.34  thf(sk_B_type, type, sk_B: $i).
% 2.16/2.34  thf(sk_C_type, type, sk_C: $i).
% 2.16/2.34  thf(t149_zfmisc_1, conjecture,
% 2.16/2.34    (![A:$i,B:$i,C:$i,D:$i]:
% 2.16/2.34     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.16/2.34         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.16/2.34       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.16/2.34  thf(zf_stmt_0, negated_conjecture,
% 2.16/2.34    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.16/2.34        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.16/2.34            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.16/2.34          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.16/2.34    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.16/2.34  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 2.16/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.16/2.34  thf('1', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 2.16/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.16/2.34  thf(symmetry_r1_xboole_0, axiom,
% 2.16/2.34    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.16/2.34  thf('2', plain,
% 2.16/2.34      (![X8 : $i, X9 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 2.16/2.34      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.16/2.34  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 2.16/2.34      inference('sup-', [status(thm)], ['1', '2'])).
% 2.16/2.34  thf('4', plain, ((r2_hidden @ sk_D_1 @ sk_C)),
% 2.16/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.16/2.34  thf(t65_zfmisc_1, axiom,
% 2.16/2.34    (![A:$i,B:$i]:
% 2.16/2.34     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.16/2.34       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.16/2.34  thf('5', plain,
% 2.16/2.34      (![X39 : $i, X40 : $i]:
% 2.16/2.34         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 2.16/2.34          | (r2_hidden @ X40 @ X39))),
% 2.16/2.34      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.16/2.34  thf(t79_xboole_1, axiom,
% 2.16/2.34    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.16/2.34  thf('6', plain,
% 2.16/2.34      (![X25 : $i, X26 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X26)),
% 2.16/2.34      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.16/2.34  thf('7', plain,
% 2.16/2.34      (![X8 : $i, X9 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 2.16/2.34      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.16/2.34  thf('8', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.16/2.34      inference('sup-', [status(thm)], ['6', '7'])).
% 2.16/2.34  thf('9', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 2.16/2.34      inference('sup+', [status(thm)], ['5', '8'])).
% 2.16/2.34  thf(t70_xboole_1, axiom,
% 2.16/2.34    (![A:$i,B:$i,C:$i]:
% 2.16/2.34     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.16/2.34            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.16/2.34       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.16/2.34            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.16/2.34  thf('10', plain,
% 2.16/2.34      (![X21 : $i, X22 : $i, X24 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ X21 @ X22)
% 2.16/2.34          | ~ (r1_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X24)))),
% 2.16/2.34      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.16/2.34  thf('11', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.34         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.16/2.34          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 2.16/2.34      inference('sup-', [status(thm)], ['9', '10'])).
% 2.16/2.34  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.16/2.34  thf('12', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 2.16/2.34      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.16/2.34  thf('13', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 2.16/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.16/2.34  thf('14', plain,
% 2.16/2.34      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 2.16/2.34          | ~ (r1_xboole_0 @ X21 @ X22)
% 2.16/2.34          | ~ (r1_xboole_0 @ X21 @ X23))),
% 2.16/2.34      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.16/2.34  thf('15', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         (~ (r1_xboole_0 @ sk_C @ X0)
% 2.16/2.34          | (r1_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 2.16/2.34      inference('sup-', [status(thm)], ['13', '14'])).
% 2.16/2.34  thf('16', plain, ((r1_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 2.16/2.34      inference('sup-', [status(thm)], ['12', '15'])).
% 2.16/2.34  thf(t83_xboole_1, axiom,
% 2.16/2.34    (![A:$i,B:$i]:
% 2.16/2.34     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.16/2.34  thf('17', plain,
% 2.16/2.34      (![X27 : $i, X28 : $i]:
% 2.16/2.34         (((k4_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_xboole_0 @ X27 @ X28))),
% 2.16/2.34      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.16/2.34  thf('18', plain,
% 2.16/2.34      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ k1_xboole_0)) = (sk_C))),
% 2.16/2.34      inference('sup-', [status(thm)], ['16', '17'])).
% 2.16/2.34  thf(d5_xboole_0, axiom,
% 2.16/2.34    (![A:$i,B:$i,C:$i]:
% 2.16/2.34     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.16/2.34       ( ![D:$i]:
% 2.16/2.34         ( ( r2_hidden @ D @ C ) <=>
% 2.16/2.34           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.16/2.34  thf('19', plain,
% 2.16/2.34      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.16/2.34         (~ (r2_hidden @ X6 @ X5)
% 2.16/2.34          | ~ (r2_hidden @ X6 @ X4)
% 2.16/2.34          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 2.16/2.34      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.16/2.34  thf('20', plain,
% 2.16/2.34      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.16/2.34         (~ (r2_hidden @ X6 @ X4)
% 2.16/2.34          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.16/2.34      inference('simplify', [status(thm)], ['19'])).
% 2.16/2.34  thf('21', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         (~ (r2_hidden @ X0 @ sk_C)
% 2.16/2.34          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B @ k1_xboole_0)))),
% 2.16/2.34      inference('sup-', [status(thm)], ['18', '20'])).
% 2.16/2.34  thf('22', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ (k1_tarski @ X0) @ sk_B) | ~ (r2_hidden @ X0 @ sk_C))),
% 2.16/2.34      inference('sup-', [status(thm)], ['11', '21'])).
% 2.16/2.34  thf('23', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_B)),
% 2.16/2.34      inference('sup-', [status(thm)], ['4', '22'])).
% 2.16/2.34  thf('24', plain,
% 2.16/2.34      (![X8 : $i, X9 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 2.16/2.34      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.16/2.34  thf('25', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1))),
% 2.16/2.34      inference('sup-', [status(thm)], ['23', '24'])).
% 2.16/2.34  thf('26', plain,
% 2.16/2.34      (![X27 : $i, X28 : $i]:
% 2.16/2.34         (((k4_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_xboole_0 @ X27 @ X28))),
% 2.16/2.34      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.16/2.34  thf('27', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)) = (sk_B))),
% 2.16/2.34      inference('sup-', [status(thm)], ['25', '26'])).
% 2.16/2.34  thf(t48_xboole_1, axiom,
% 2.16/2.34    (![A:$i,B:$i]:
% 2.16/2.34     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.16/2.34  thf('28', plain,
% 2.16/2.34      (![X18 : $i, X19 : $i]:
% 2.16/2.34         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.16/2.34           = (k3_xboole_0 @ X18 @ X19))),
% 2.16/2.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.16/2.34  thf('29', plain,
% 2.16/2.34      (((k4_xboole_0 @ sk_B @ sk_B)
% 2.16/2.34         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)))),
% 2.16/2.34      inference('sup+', [status(thm)], ['27', '28'])).
% 2.16/2.34  thf(t3_boole, axiom,
% 2.16/2.34    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.16/2.34  thf('30', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 2.16/2.34      inference('cnf', [status(esa)], [t3_boole])).
% 2.16/2.34  thf('31', plain,
% 2.16/2.34      (![X18 : $i, X19 : $i]:
% 2.16/2.34         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.16/2.34           = (k3_xboole_0 @ X18 @ X19))),
% 2.16/2.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.16/2.34  thf('32', plain,
% 2.16/2.34      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.16/2.34      inference('sup+', [status(thm)], ['30', '31'])).
% 2.16/2.34  thf('33', plain,
% 2.16/2.34      (![X18 : $i, X19 : $i]:
% 2.16/2.34         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.16/2.34           = (k3_xboole_0 @ X18 @ X19))),
% 2.16/2.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.16/2.34  thf('34', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 2.16/2.34      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.16/2.34  thf('35', plain,
% 2.16/2.34      (![X8 : $i, X9 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 2.16/2.34      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.16/2.34  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.16/2.34      inference('sup-', [status(thm)], ['34', '35'])).
% 2.16/2.34  thf('37', plain,
% 2.16/2.34      (![X27 : $i, X28 : $i]:
% 2.16/2.34         (((k4_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_xboole_0 @ X27 @ X28))),
% 2.16/2.34      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.16/2.34  thf('38', plain,
% 2.16/2.34      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.16/2.34      inference('sup-', [status(thm)], ['36', '37'])).
% 2.16/2.34  thf('39', plain,
% 2.16/2.34      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.16/2.34      inference('sup+', [status(thm)], ['33', '38'])).
% 2.16/2.34  thf(commutativity_k3_xboole_0, axiom,
% 2.16/2.34    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.16/2.34  thf('40', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.16/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.16/2.34  thf('41', plain,
% 2.16/2.34      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.16/2.34      inference('sup+', [status(thm)], ['39', '40'])).
% 2.16/2.34  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.16/2.34      inference('demod', [status(thm)], ['32', '41'])).
% 2.16/2.34  thf('43', plain,
% 2.16/2.34      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)))),
% 2.16/2.34      inference('demod', [status(thm)], ['29', '42'])).
% 2.16/2.34  thf(t16_xboole_1, axiom,
% 2.16/2.34    (![A:$i,B:$i,C:$i]:
% 2.16/2.34     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.16/2.34       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.16/2.34  thf('44', plain,
% 2.16/2.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 2.16/2.34           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.16/2.34      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.16/2.34  thf('45', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 2.16/2.34           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)))),
% 2.16/2.34      inference('sup+', [status(thm)], ['43', '44'])).
% 2.16/2.34  thf('46', plain,
% 2.16/2.34      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.16/2.34      inference('sup+', [status(thm)], ['33', '38'])).
% 2.16/2.34  thf('47', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         ((k1_xboole_0)
% 2.16/2.34           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ X0)))),
% 2.16/2.34      inference('demod', [status(thm)], ['45', '46'])).
% 2.16/2.34  thf('48', plain,
% 2.16/2.34      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 2.16/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.16/2.34  thf('49', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.16/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.16/2.34  thf('50', plain,
% 2.16/2.34      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 2.16/2.34      inference('demod', [status(thm)], ['48', '49'])).
% 2.16/2.34  thf(t28_xboole_1, axiom,
% 2.16/2.34    (![A:$i,B:$i]:
% 2.16/2.34     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.16/2.34  thf('51', plain,
% 2.16/2.34      (![X13 : $i, X14 : $i]:
% 2.16/2.34         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 2.16/2.34      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.16/2.34  thf('52', plain,
% 2.16/2.34      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 2.16/2.34         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.16/2.34      inference('sup-', [status(thm)], ['50', '51'])).
% 2.16/2.34  thf('53', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.16/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.16/2.34  thf('54', plain,
% 2.16/2.34      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A))
% 2.16/2.34         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.16/2.34      inference('demod', [status(thm)], ['52', '53'])).
% 2.16/2.34  thf('55', plain,
% 2.16/2.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 2.16/2.34           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.16/2.34      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.16/2.34  thf('56', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 2.16/2.34           = (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ 
% 2.16/2.34              (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)))),
% 2.16/2.34      inference('sup+', [status(thm)], ['54', '55'])).
% 2.16/2.34  thf('57', plain,
% 2.16/2.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 2.16/2.34           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.16/2.34      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.16/2.34  thf('58', plain,
% 2.16/2.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 2.16/2.34           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.16/2.34      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.16/2.34  thf('59', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 2.16/2.34           = (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ 
% 2.16/2.34              (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))))),
% 2.16/2.34      inference('demod', [status(thm)], ['56', '57', '58'])).
% 2.16/2.34  thf('60', plain,
% 2.16/2.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 2.16/2.34           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.16/2.34      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.16/2.34  thf('61', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.16/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.16/2.34  thf('62', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 2.16/2.34           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.16/2.34      inference('sup+', [status(thm)], ['60', '61'])).
% 2.16/2.34  thf('63', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.16/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.16/2.34  thf('64', plain,
% 2.16/2.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 2.16/2.34           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.16/2.34      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.16/2.34  thf('65', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.16/2.34           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.16/2.34      inference('sup+', [status(thm)], ['63', '64'])).
% 2.16/2.34  thf('66', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 2.16/2.34           = (k3_xboole_0 @ sk_B @ 
% 2.16/2.34              (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))))),
% 2.16/2.34      inference('demod', [status(thm)], ['59', '62', '65'])).
% 2.16/2.34  thf('67', plain,
% 2.16/2.34      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))
% 2.16/2.34         = (k1_xboole_0))),
% 2.16/2.34      inference('sup+', [status(thm)], ['47', '66'])).
% 2.16/2.34  thf('68', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 2.16/2.34           = (k3_xboole_0 @ sk_B @ 
% 2.16/2.34              (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))))),
% 2.16/2.34      inference('demod', [status(thm)], ['59', '62', '65'])).
% 2.16/2.34  thf('69', plain,
% 2.16/2.34      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))
% 2.16/2.34         = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 2.16/2.34      inference('sup+', [status(thm)], ['67', '68'])).
% 2.16/2.34  thf('70', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.16/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.16/2.34  thf('71', plain,
% 2.16/2.34      (![X18 : $i, X19 : $i]:
% 2.16/2.34         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.16/2.34           = (k3_xboole_0 @ X18 @ X19))),
% 2.16/2.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.16/2.34  thf('72', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.16/2.34      inference('sup-', [status(thm)], ['6', '7'])).
% 2.16/2.34  thf('73', plain,
% 2.16/2.34      (![X27 : $i, X28 : $i]:
% 2.16/2.34         (((k4_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_xboole_0 @ X27 @ X28))),
% 2.16/2.34      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.16/2.34  thf('74', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]:
% 2.16/2.34         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.16/2.34      inference('sup-', [status(thm)], ['72', '73'])).
% 2.16/2.34  thf('75', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.16/2.34      inference('sup+', [status(thm)], ['71', '74'])).
% 2.16/2.34  thf('76', plain,
% 2.16/2.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 2.16/2.34           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.16/2.34      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.16/2.34  thf('77', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i]:
% 2.16/2.34         ((k3_xboole_0 @ X0 @ X1)
% 2.16/2.34           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.16/2.34      inference('sup+', [status(thm)], ['75', '76'])).
% 2.16/2.34  thf('78', plain,
% 2.16/2.34      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.16/2.34      inference('sup+', [status(thm)], ['39', '40'])).
% 2.16/2.34  thf('79', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 2.16/2.34      inference('demod', [status(thm)], ['69', '70', '77', '78'])).
% 2.16/2.34  thf(t47_xboole_1, axiom,
% 2.16/2.34    (![A:$i,B:$i]:
% 2.16/2.34     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.16/2.34  thf('80', plain,
% 2.16/2.34      (![X16 : $i, X17 : $i]:
% 2.16/2.34         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 2.16/2.34           = (k4_xboole_0 @ X16 @ X17))),
% 2.16/2.34      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.16/2.34  thf('81', plain,
% 2.16/2.34      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_A))),
% 2.16/2.34      inference('sup+', [status(thm)], ['79', '80'])).
% 2.16/2.34  thf('82', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 2.16/2.34      inference('cnf', [status(esa)], [t3_boole])).
% 2.16/2.34  thf('83', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 2.16/2.34      inference('demod', [status(thm)], ['81', '82'])).
% 2.16/2.34  thf('84', plain,
% 2.16/2.34      (![X25 : $i, X26 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X26)),
% 2.16/2.34      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.16/2.34  thf('85', plain,
% 2.16/2.34      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 2.16/2.34          | ~ (r1_xboole_0 @ X21 @ X22)
% 2.16/2.34          | ~ (r1_xboole_0 @ X21 @ X23))),
% 2.16/2.34      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.16/2.34  thf('86', plain,
% 2.16/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.16/2.34         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.16/2.34          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 2.16/2.34      inference('sup-', [status(thm)], ['84', '85'])).
% 2.16/2.34  thf('87', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         (~ (r1_xboole_0 @ sk_B @ X0)
% 2.16/2.34          | (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 2.16/2.34             (k2_xboole_0 @ sk_A @ X0)))),
% 2.16/2.34      inference('sup-', [status(thm)], ['83', '86'])).
% 2.16/2.34  thf('88', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 2.16/2.34      inference('demod', [status(thm)], ['81', '82'])).
% 2.16/2.34  thf('89', plain,
% 2.16/2.34      (![X0 : $i]:
% 2.16/2.34         (~ (r1_xboole_0 @ sk_B @ X0)
% 2.16/2.34          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.16/2.34      inference('demod', [status(thm)], ['87', '88'])).
% 2.16/2.34  thf('90', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C))),
% 2.16/2.34      inference('sup-', [status(thm)], ['3', '89'])).
% 2.16/2.34  thf('91', plain,
% 2.16/2.34      (![X8 : $i, X9 : $i]:
% 2.16/2.34         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 2.16/2.34      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.16/2.34  thf('92', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 2.16/2.34      inference('sup-', [status(thm)], ['90', '91'])).
% 2.16/2.34  thf('93', plain, ($false), inference('demod', [status(thm)], ['0', '92'])).
% 2.16/2.34  
% 2.16/2.34  % SZS output end Refutation
% 2.16/2.34  
% 2.16/2.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
