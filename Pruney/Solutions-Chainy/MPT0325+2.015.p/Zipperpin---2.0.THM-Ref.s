%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RlsUbeB5EE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:42 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 235 expanded)
%              Number of leaves         :   22 (  80 expanded)
%              Depth                    :   20
%              Number of atoms          :  851 (2165 expanded)
%              Number of equality atoms :   79 ( 180 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X24 @ X26 ) @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X27 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('24',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X21 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
      | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('36',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('44',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_B @ sk_D_1 )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('51',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_zfmisc_1 @ X19 @ X20 )
        = k1_xboole_0 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['51','53'])).

thf('55',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('61',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X26 @ X24 ) @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('64',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X22 @ X21 ) @ ( k2_zfmisc_1 @ X23 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
      | ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('68',plain,
    ( ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('70',plain,
    ( ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('72',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_zfmisc_1 @ X19 @ X20 )
        = k1_xboole_0 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,(
    ! [X19: $i] :
      ( ( k2_zfmisc_1 @ X19 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','74'])).

thf('76',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['59','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RlsUbeB5EE
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:53:33 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 1.06/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.28  % Solved by: fo/fo7.sh
% 1.06/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.28  % done 955 iterations in 0.836s
% 1.06/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.28  % SZS output start Refutation
% 1.06/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.28  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.06/1.28  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.06/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.06/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.28  thf(t138_zfmisc_1, conjecture,
% 1.06/1.28    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.28     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.06/1.28       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 1.06/1.28         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 1.06/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.28    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.28        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.06/1.28          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 1.06/1.28            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 1.06/1.28    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 1.06/1.28  thf('0', plain,
% 1.06/1.28      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('1', plain,
% 1.06/1.28      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 1.06/1.28      inference('split', [status(esa)], ['0'])).
% 1.06/1.28  thf(commutativity_k3_xboole_0, axiom,
% 1.06/1.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.06/1.28  thf('2', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.28  thf(t48_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.06/1.28  thf('3', plain,
% 1.06/1.28      (![X16 : $i, X17 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.06/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.06/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.28  thf(d3_tarski, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( r1_tarski @ A @ B ) <=>
% 1.06/1.28       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.06/1.28  thf('4', plain,
% 1.06/1.28      (![X3 : $i, X5 : $i]:
% 1.06/1.28         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf(d5_xboole_0, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.06/1.28       ( ![D:$i]:
% 1.06/1.28         ( ( r2_hidden @ D @ C ) <=>
% 1.06/1.28           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.06/1.28  thf('5', plain,
% 1.06/1.28      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X10 @ X9)
% 1.06/1.28          | (r2_hidden @ X10 @ X7)
% 1.06/1.28          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.06/1.28  thf('6', plain,
% 1.06/1.28      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.06/1.28         ((r2_hidden @ X10 @ X7)
% 1.06/1.28          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['5'])).
% 1.06/1.28  thf('7', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.06/1.28          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['4', '6'])).
% 1.06/1.28  thf('8', plain,
% 1.06/1.28      (![X3 : $i, X5 : $i]:
% 1.06/1.28         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf('9', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.06/1.28          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.28  thf('10', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.06/1.28      inference('simplify', [status(thm)], ['9'])).
% 1.06/1.28  thf('11', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.06/1.28      inference('sup+', [status(thm)], ['3', '10'])).
% 1.06/1.28  thf('12', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.06/1.28      inference('sup+', [status(thm)], ['2', '11'])).
% 1.06/1.28  thf(t118_zfmisc_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( r1_tarski @ A @ B ) =>
% 1.06/1.28       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 1.06/1.28         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 1.06/1.28  thf('13', plain,
% 1.06/1.28      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.28         (~ (r1_tarski @ X24 @ X25)
% 1.06/1.28          | (r1_tarski @ (k2_zfmisc_1 @ X24 @ X26) @ (k2_zfmisc_1 @ X25 @ X26)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 1.06/1.28  thf('14', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 1.06/1.28          (k2_zfmisc_1 @ X0 @ X2))),
% 1.06/1.28      inference('sup-', [status(thm)], ['12', '13'])).
% 1.06/1.28  thf('15', plain,
% 1.06/1.28      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.28        (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(l32_xboole_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.28  thf('16', plain,
% 1.06/1.28      (![X12 : $i, X14 : $i]:
% 1.06/1.28         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 1.06/1.28          | ~ (r1_tarski @ X12 @ X14))),
% 1.06/1.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.28  thf('17', plain,
% 1.06/1.28      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.28         (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)) = (k1_xboole_0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['15', '16'])).
% 1.06/1.28  thf('18', plain,
% 1.06/1.28      (![X16 : $i, X17 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.06/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.06/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.28  thf('19', plain,
% 1.06/1.28      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.06/1.28         = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.28            (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.28  thf(t3_boole, axiom,
% 1.06/1.28    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.28  thf('20', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.06/1.28      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.28  thf('21', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.28  thf('22', plain,
% 1.06/1.28      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.06/1.28         = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 1.06/1.28            (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.06/1.28  thf(t123_zfmisc_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.28     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 1.06/1.28       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 1.06/1.28  thf('23', plain,
% 1.06/1.28      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.06/1.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X27 @ X29) @ (k3_xboole_0 @ X28 @ X30))
% 1.06/1.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 1.06/1.28              (k2_zfmisc_1 @ X29 @ X30)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.06/1.28  thf('24', plain,
% 1.06/1.28      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.06/1.28         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 1.06/1.28            (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['22', '23'])).
% 1.06/1.28  thf(t117_zfmisc_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.06/1.28          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 1.06/1.28            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 1.06/1.28          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 1.06/1.28  thf('25', plain,
% 1.06/1.28      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.06/1.28         (((X21) = (k1_xboole_0))
% 1.06/1.28          | (r1_tarski @ X22 @ X23)
% 1.06/1.28          | ~ (r1_tarski @ (k2_zfmisc_1 @ X21 @ X22) @ 
% 1.06/1.28               (k2_zfmisc_1 @ X21 @ X23)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.06/1.28  thf('26', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ X0) @ 
% 1.06/1.28             (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.06/1.28          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B))
% 1.06/1.28          | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['24', '25'])).
% 1.06/1.28  thf('27', plain,
% 1.06/1.28      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 1.06/1.28        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['14', '26'])).
% 1.06/1.28  thf('28', plain,
% 1.06/1.28      (![X12 : $i, X14 : $i]:
% 1.06/1.28         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 1.06/1.28          | ~ (r1_tarski @ X12 @ X14))),
% 1.06/1.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.28  thf('29', plain,
% 1.06/1.28      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 1.06/1.28        | ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D_1 @ sk_B)) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['27', '28'])).
% 1.06/1.28  thf('30', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.28  thf('31', plain,
% 1.06/1.28      (![X16 : $i, X17 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.06/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.06/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.28  thf('32', plain,
% 1.06/1.28      (![X16 : $i, X17 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.06/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.06/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.28  thf('33', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.06/1.28           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['31', '32'])).
% 1.06/1.28  thf('34', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.06/1.28           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['30', '33'])).
% 1.06/1.28  thf('35', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.06/1.28      inference('simplify', [status(thm)], ['9'])).
% 1.06/1.28  thf('36', plain,
% 1.06/1.28      (![X12 : $i, X14 : $i]:
% 1.06/1.28         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 1.06/1.28          | ~ (r1_tarski @ X12 @ X14))),
% 1.06/1.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.28  thf('37', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['35', '36'])).
% 1.06/1.28  thf('38', plain,
% 1.06/1.28      (![X16 : $i, X17 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.06/1.28           = (k3_xboole_0 @ X16 @ X17))),
% 1.06/1.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.28  thf('39', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 1.06/1.28           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.06/1.28      inference('sup+', [status(thm)], ['37', '38'])).
% 1.06/1.28  thf('40', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.06/1.28      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.28  thf('41', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.28  thf('42', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.28           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.06/1.28      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.06/1.28  thf('43', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.06/1.28           = (k4_xboole_0 @ X0 @ X1))),
% 1.06/1.28      inference('demod', [status(thm)], ['34', '42'])).
% 1.06/1.28  thf('44', plain,
% 1.06/1.28      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 1.06/1.28        | ((k4_xboole_0 @ sk_B @ sk_D_1) = (k1_xboole_0)))),
% 1.06/1.28      inference('demod', [status(thm)], ['29', '43'])).
% 1.06/1.28  thf('45', plain,
% 1.06/1.28      (![X12 : $i, X13 : $i]:
% 1.06/1.28         ((r1_tarski @ X12 @ X13)
% 1.06/1.28          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 1.06/1.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.28  thf('46', plain,
% 1.06/1.28      ((((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.28        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 1.06/1.28        | (r1_tarski @ sk_B @ sk_D_1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['44', '45'])).
% 1.06/1.28  thf('47', plain,
% 1.06/1.28      (((r1_tarski @ sk_B @ sk_D_1)
% 1.06/1.28        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['46'])).
% 1.06/1.28  thf('48', plain,
% 1.06/1.28      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 1.06/1.28      inference('split', [status(esa)], ['0'])).
% 1.06/1.28  thf('49', plain,
% 1.06/1.28      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))
% 1.06/1.28         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['47', '48'])).
% 1.06/1.28  thf('50', plain,
% 1.06/1.28      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.06/1.28         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 1.06/1.28            (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['22', '23'])).
% 1.06/1.28  thf('51', plain,
% 1.06/1.28      ((((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_D_1 @ sk_B))))
% 1.06/1.28         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['49', '50'])).
% 1.06/1.28  thf(t113_zfmisc_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.06/1.28       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.06/1.28  thf('52', plain,
% 1.06/1.28      (![X19 : $i, X20 : $i]:
% 1.06/1.28         (((k2_zfmisc_1 @ X19 @ X20) = (k1_xboole_0))
% 1.06/1.28          | ((X19) != (k1_xboole_0)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.06/1.28  thf('53', plain,
% 1.06/1.28      (![X20 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['52'])).
% 1.06/1.28  thf('54', plain,
% 1.06/1.28      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.06/1.28         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 1.06/1.28      inference('demod', [status(thm)], ['51', '53'])).
% 1.06/1.28  thf('55', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('56', plain, (((r1_tarski @ sk_B @ sk_D_1))),
% 1.06/1.28      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 1.06/1.28  thf('57', plain,
% 1.06/1.28      (~ ((r1_tarski @ sk_A @ sk_C_1)) | ~ ((r1_tarski @ sk_B @ sk_D_1))),
% 1.06/1.28      inference('split', [status(esa)], ['0'])).
% 1.06/1.28  thf('58', plain, (~ ((r1_tarski @ sk_A @ sk_C_1))),
% 1.06/1.28      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 1.06/1.28  thf('59', plain, (~ (r1_tarski @ sk_A @ sk_C_1)),
% 1.06/1.28      inference('simpl_trail', [status(thm)], ['1', '58'])).
% 1.06/1.28  thf('60', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.06/1.28      inference('sup+', [status(thm)], ['2', '11'])).
% 1.06/1.28  thf('61', plain,
% 1.06/1.28      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.28         (~ (r1_tarski @ X24 @ X25)
% 1.06/1.28          | (r1_tarski @ (k2_zfmisc_1 @ X26 @ X24) @ (k2_zfmisc_1 @ X26 @ X25)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 1.06/1.28  thf('62', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.06/1.28          (k2_zfmisc_1 @ X2 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.28  thf('63', plain,
% 1.06/1.28      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.06/1.28         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 1.06/1.28            (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['22', '23'])).
% 1.06/1.28  thf('64', plain,
% 1.06/1.28      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.06/1.28         (((X21) = (k1_xboole_0))
% 1.06/1.28          | (r1_tarski @ X22 @ X23)
% 1.06/1.28          | ~ (r1_tarski @ (k2_zfmisc_1 @ X22 @ X21) @ 
% 1.06/1.28               (k2_zfmisc_1 @ X23 @ X21)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.06/1.28  thf('65', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B)) @ 
% 1.06/1.28             (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.06/1.28          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_C_1 @ sk_A))
% 1.06/1.28          | ((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['63', '64'])).
% 1.06/1.28  thf('66', plain,
% 1.06/1.28      ((((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0))
% 1.06/1.28        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['62', '65'])).
% 1.06/1.28  thf('67', plain,
% 1.06/1.28      (![X12 : $i, X14 : $i]:
% 1.06/1.28         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 1.06/1.28          | ~ (r1_tarski @ X12 @ X14))),
% 1.06/1.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.28  thf('68', plain,
% 1.06/1.28      ((((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0))
% 1.06/1.28        | ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['66', '67'])).
% 1.06/1.28  thf('69', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.06/1.28           = (k4_xboole_0 @ X0 @ X1))),
% 1.06/1.28      inference('demod', [status(thm)], ['34', '42'])).
% 1.06/1.28  thf('70', plain,
% 1.06/1.28      ((((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0))
% 1.06/1.28        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 1.06/1.28      inference('demod', [status(thm)], ['68', '69'])).
% 1.06/1.28  thf('71', plain,
% 1.06/1.28      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.06/1.28         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 1.06/1.28            (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 1.06/1.28      inference('demod', [status(thm)], ['22', '23'])).
% 1.06/1.28  thf('72', plain,
% 1.06/1.28      ((((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.06/1.28          = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ k1_xboole_0))
% 1.06/1.28        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['70', '71'])).
% 1.06/1.28  thf('73', plain,
% 1.06/1.28      (![X19 : $i, X20 : $i]:
% 1.06/1.28         (((k2_zfmisc_1 @ X19 @ X20) = (k1_xboole_0))
% 1.06/1.28          | ((X20) != (k1_xboole_0)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.06/1.28  thf('74', plain,
% 1.06/1.28      (![X19 : $i]: ((k2_zfmisc_1 @ X19 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['73'])).
% 1.06/1.28  thf('75', plain,
% 1.06/1.28      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.06/1.28        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 1.06/1.28      inference('demod', [status(thm)], ['72', '74'])).
% 1.06/1.28  thf('76', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('77', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 1.06/1.28      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 1.06/1.28  thf('78', plain,
% 1.06/1.28      (![X12 : $i, X13 : $i]:
% 1.06/1.28         ((r1_tarski @ X12 @ X13)
% 1.06/1.28          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 1.06/1.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.28  thf('79', plain,
% 1.06/1.28      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_C_1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['77', '78'])).
% 1.06/1.28  thf('80', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 1.06/1.28      inference('simplify', [status(thm)], ['79'])).
% 1.06/1.28  thf('81', plain, ($false), inference('demod', [status(thm)], ['59', '80'])).
% 1.06/1.28  
% 1.06/1.28  % SZS output end Refutation
% 1.06/1.28  
% 1.06/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
