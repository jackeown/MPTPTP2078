%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DSruMJYOkN

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 266 expanded)
%              Number of leaves         :   28 (  85 expanded)
%              Depth                    :   21
%              Number of atoms          :  676 (2668 expanded)
%              Number of equality atoms :  101 ( 498 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( k3_xboole_0 @ X22 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('14',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X56 ) @ X57 )
      | ( r2_hidden @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('15',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('28',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k3_xboole_0 @ X59 @ ( k1_tarski @ X58 ) )
        = ( k1_tarski @ X58 ) )
      | ~ ( r2_hidden @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('29',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('34',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X56 ) @ X57 )
      | ( r2_hidden @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('37',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k3_xboole_0 @ X59 @ ( k1_tarski @ X58 ) )
        = ( k1_tarski @ X58 ) )
      | ~ ( r2_hidden @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('47',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('49',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','58'])).

thf('60',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('63',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('66',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('67',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['62','64','68'])).

thf('70',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['61','69'])).

thf('71',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['59','70'])).

thf('72',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('73',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','73'])).

thf('75',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['29','74'])).

thf('76',plain,
    ( sk_C_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['12','75'])).

thf('77',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['61','69'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DSruMJYOkN
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 457 iterations in 0.143s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.60  thf(t43_zfmisc_1, conjecture,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.60          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.60          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.60          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.60        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.60             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.60             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.60             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.21/0.60  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(t2_boole, axiom,
% 0.21/0.60    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.60  thf('1', plain,
% 0.21/0.60      (![X22 : $i]: ((k3_xboole_0 @ X22 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.60  thf(t100_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      (![X10 : $i, X11 : $i]:
% 0.21/0.60         ((k4_xboole_0 @ X10 @ X11)
% 0.21/0.60           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.60      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.60  thf(t5_boole, axiom,
% 0.21/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.60  thf('4', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 0.21/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.60  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.60  thf(t36_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.60  thf('6', plain,
% 0.21/0.60      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 0.21/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.60  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.60  thf(t10_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.21/0.60  thf('8', plain,
% 0.21/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.60         (~ (r1_tarski @ X12 @ X13)
% 0.21/0.60          | (r1_tarski @ X12 @ (k2_xboole_0 @ X14 @ X13)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.21/0.60  thf('9', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.60  thf('10', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.21/0.60      inference('sup+', [status(thm)], ['0', '9'])).
% 0.21/0.60  thf(t28_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.60  thf('11', plain,
% 0.21/0.60      (![X20 : $i, X21 : $i]:
% 0.21/0.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.21/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.60  thf('12', plain, (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (sk_C_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.60  thf(t7_xboole_0, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.60  thf('13', plain,
% 0.21/0.60      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.60  thf(l27_zfmisc_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      (![X56 : $i, X57 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ (k1_tarski @ X56) @ X57) | (r2_hidden @ X56 @ X57))),
% 0.21/0.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.60  thf('15', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.21/0.60      inference('sup+', [status(thm)], ['0', '9'])).
% 0.21/0.60  thf(t12_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      (![X15 : $i, X16 : $i]:
% 0.21/0.60         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.21/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.60  thf('17', plain,
% 0.21/0.60      (((k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.60  thf(t7_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      (![X20 : $i, X21 : $i]:
% 0.21/0.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.21/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.60  thf('20', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.60  thf('21', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.60  thf(t4_xboole_0, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.21/0.60          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.60  thf('23', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.60          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.60  thf('24', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.60          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1)
% 0.21/0.60          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['17', '24'])).
% 0.21/0.60  thf('26', plain,
% 0.21/0.60      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['14', '25'])).
% 0.21/0.60  thf('27', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_C_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['13', '26'])).
% 0.21/0.60  thf(l31_zfmisc_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.60       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.21/0.60  thf('28', plain,
% 0.21/0.60      (![X58 : $i, X59 : $i]:
% 0.21/0.60         (((k3_xboole_0 @ X59 @ (k1_tarski @ X58)) = (k1_tarski @ X58))
% 0.21/0.60          | ~ (r2_hidden @ X58 @ X59))),
% 0.21/0.60      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | ((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('31', plain,
% 0.21/0.60      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.21/0.60      inference('split', [status(esa)], ['30'])).
% 0.21/0.60  thf('32', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('33', plain,
% 0.21/0.60      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.60  thf('34', plain,
% 0.21/0.60      (![X56 : $i, X57 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ (k1_tarski @ X56) @ X57) | (r2_hidden @ X56 @ X57))),
% 0.21/0.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.60  thf('35', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('36', plain,
% 0.21/0.60      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.60  thf('37', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.21/0.60      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.60  thf('38', plain,
% 0.21/0.60      (![X20 : $i, X21 : $i]:
% 0.21/0.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.21/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.60  thf('39', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.60  thf('40', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.60          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.60  thf('41', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.21/0.60          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.60  thf('42', plain,
% 0.21/0.60      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['34', '41'])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['33', '42'])).
% 0.21/0.60  thf('44', plain,
% 0.21/0.60      (![X58 : $i, X59 : $i]:
% 0.21/0.60         (((k3_xboole_0 @ X59 @ (k1_tarski @ X58)) = (k1_tarski @ X58))
% 0.21/0.60          | ~ (r2_hidden @ X58 @ X59))),
% 0.21/0.60      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.21/0.60  thf('45', plain,
% 0.21/0.60      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.60        | ((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.60  thf('46', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.60  thf('47', plain,
% 0.21/0.60      ((((k1_tarski @ sk_A) = (sk_B_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['45', '46'])).
% 0.21/0.60  thf('48', plain,
% 0.21/0.60      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.21/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.60      inference('split', [status(esa)], ['30'])).
% 0.21/0.60  thf('49', plain,
% 0.21/0.60      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.60  thf('50', plain,
% 0.21/0.60      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.60      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.60  thf('51', plain,
% 0.21/0.60      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.60  thf(l32_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.60  thf('52', plain,
% 0.21/0.60      (![X7 : $i, X9 : $i]:
% 0.21/0.60         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.60  thf('53', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.60  thf('54', plain,
% 0.21/0.60      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 0.21/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.60  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.60      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.60  thf('56', plain,
% 0.21/0.60      (![X15 : $i, X16 : $i]:
% 0.21/0.60         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.21/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.60  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.60  thf('58', plain,
% 0.21/0.60      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 0.21/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.60      inference('sup+', [status(thm)], ['50', '57'])).
% 0.21/0.60  thf('59', plain,
% 0.21/0.60      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 0.21/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.60      inference('sup+', [status(thm)], ['32', '58'])).
% 0.21/0.60  thf('60', plain,
% 0.21/0.60      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('61', plain,
% 0.21/0.60      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.21/0.60         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.21/0.60      inference('split', [status(esa)], ['60'])).
% 0.21/0.60  thf('62', plain,
% 0.21/0.60      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('split', [status(esa)], ['60'])).
% 0.21/0.60  thf('63', plain,
% 0.21/0.60      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('64', plain,
% 0.21/0.60      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.21/0.60       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('split', [status(esa)], ['63'])).
% 0.21/0.60  thf('65', plain,
% 0.21/0.60      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.60      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.60  thf('66', plain,
% 0.21/0.60      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.60      inference('split', [status(esa)], ['60'])).
% 0.21/0.60  thf('67', plain,
% 0.21/0.60      ((((sk_B_1) != (sk_B_1)))
% 0.21/0.60         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.21/0.60             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.60  thf('68', plain,
% 0.21/0.60      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.60  thf('69', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['62', '64', '68'])).
% 0.21/0.60  thf('70', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['61', '69'])).
% 0.21/0.60  thf('71', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['59', '70'])).
% 0.21/0.60  thf('72', plain,
% 0.21/0.60      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('split', [status(esa)], ['30'])).
% 0.21/0.60  thf('73', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.21/0.60  thf('74', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['31', '73'])).
% 0.21/0.60  thf('75', plain,
% 0.21/0.60      (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['29', '74'])).
% 0.21/0.60  thf('76', plain, (((sk_C_1) = (k1_tarski @ sk_A))),
% 0.21/0.60      inference('sup+', [status(thm)], ['12', '75'])).
% 0.21/0.60  thf('77', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['61', '69'])).
% 0.21/0.60  thf('78', plain, ($false),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.21/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
