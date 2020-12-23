%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1pQ52hM6Ir

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:35 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 428 expanded)
%              Number of leaves         :   30 ( 127 expanded)
%              Depth                    :   27
%              Number of atoms          :  786 (4595 expanded)
%              Number of equality atoms :  126 ( 927 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('4',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) ) )
      = X17 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X20 @ X23 )
      | ~ ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X20 @ X23 )
      | ~ ( r1_xboole_0 @ X20 @ ( k3_tarski @ ( k2_tarski @ X21 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X16 @ X15 ) )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('30',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('32',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X41
        = ( k1_tarski @ X40 ) )
      | ( X41 = k1_xboole_0 )
      | ~ ( r1_tarski @ X41 @ ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('33',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('46',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['42'])).

thf('47',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X16 @ X15 ) )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ X0 ) )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','52'])).

thf('54',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('57',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('60',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('61',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['56','58','62'])).

thf('64',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['55','63'])).

thf('65',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['53','64'])).

thf('66',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['42'])).

thf('67',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','67'])).

thf('69',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['41','68'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('70',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( X29 = X26 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('71',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('74',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','67'])).

thf('78',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','78'])).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X16 @ X15 ) )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('81',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','81'])).

thf('83',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['55','63'])).

thf('84',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['25','84'])).

thf('86',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['2','85'])).

thf('87',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['55','63'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1pQ52hM6Ir
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:46:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 577 iterations in 0.157s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.40/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(t43_zfmisc_1, conjecture,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.40/0.61          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.40/0.61          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.40/0.61          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.61        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.40/0.61             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.40/0.61             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.40/0.61             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.40/0.61  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(l51_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (![X43 : $i, X44 : $i]:
% 0.40/0.61         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.40/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.40/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.40/0.61  thf(t21_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i]:
% 0.40/0.61         ((k3_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (X17))),
% 0.40/0.61      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X43 : $i, X44 : $i]:
% 0.40/0.61         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.40/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i]:
% 0.40/0.61         ((k3_xboole_0 @ X17 @ (k3_tarski @ (k2_tarski @ X17 @ X18))) = (X17))),
% 0.40/0.61      inference('demod', [status(thm)], ['3', '4'])).
% 0.40/0.61  thf(d7_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.40/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X6 : $i, X8 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((X0) != (k1_xboole_0))
% 0.40/0.61          | (r1_xboole_0 @ X0 @ (k3_tarski @ (k2_tarski @ X0 @ X1))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X1 : $i]:
% 0.40/0.61         (r1_xboole_0 @ k1_xboole_0 @ 
% 0.40/0.61          (k3_tarski @ (k2_tarski @ k1_xboole_0 @ X1)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['7'])).
% 0.40/0.61  thf(t70_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.40/0.61            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.40/0.61       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.40/0.61            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X20 @ X23)
% 0.40/0.61          | ~ (r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X23)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X43 : $i, X44 : $i]:
% 0.40/0.61         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.40/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X20 @ X23)
% 0.40/0.61          | ~ (r1_xboole_0 @ X20 @ (k3_tarski @ (k2_tarski @ X21 @ X23))))),
% 0.40/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.61  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.40/0.61      inference('sup-', [status(thm)], ['8', '11'])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X6 : $i, X7 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.61  thf(t100_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X13 : $i, X14 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X13 @ X14)
% 0.40/0.61           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.61           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.40/0.61  thf(t5_boole, axiom,
% 0.40/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.61  thf('17', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.40/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.61  thf(l32_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X10 : $i, X11 : $i]:
% 0.40/0.61         ((r1_tarski @ X10 @ X11)
% 0.40/0.61          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.61  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.61  thf(t12_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X15 : $i, X16 : $i]:
% 0.40/0.61         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.40/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X43 : $i, X44 : $i]:
% 0.40/0.61         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.40/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (![X15 : $i, X16 : $i]:
% 0.40/0.61         (((k3_tarski @ (k2_tarski @ X16 @ X15)) = (X15))
% 0.40/0.61          | ~ (r1_tarski @ X16 @ X15))),
% 0.40/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['21', '24'])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.40/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.40/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.40/0.61  thf(t7_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 0.40/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X43 : $i, X44 : $i]:
% 0.40/0.61         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.40/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (![X24 : $i, X25 : $i]:
% 0.40/0.61         (r1_tarski @ X24 @ (k3_tarski @ (k2_tarski @ X24 @ X25)))),
% 0.40/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.61  thf('31', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['27', '30'])).
% 0.40/0.61  thf(l3_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.40/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      (![X40 : $i, X41 : $i]:
% 0.40/0.61         (((X41) = (k1_tarski @ X40))
% 0.40/0.61          | ((X41) = (k1_xboole_0))
% 0.40/0.61          | ~ (r1_tarski @ X41 @ (k1_tarski @ X40)))),
% 0.40/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.40/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.40/0.61  thf(t7_xboole_0, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.61  thf('35', plain,
% 0.40/0.61      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.40/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.61  thf(d3_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.40/0.61       ( ![D:$i]:
% 0.40/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.61           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.61          | (r2_hidden @ X0 @ X2)
% 0.40/0.61          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.40/0.61         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['36'])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      (![X43 : $i, X44 : $i]:
% 0.40/0.61         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.40/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.40/0.61         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.40/0.61          | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.61      inference('demod', [status(thm)], ['37', '38'])).
% 0.40/0.61  thf('40', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((X0) = (k1_xboole_0))
% 0.40/0.61          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['35', '39'])).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.40/0.61        | ((sk_C_1) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['34', '40'])).
% 0.40/0.61  thf('42', plain,
% 0.40/0.61      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('43', plain,
% 0.40/0.61      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.40/0.61      inference('split', [status(esa)], ['42'])).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.40/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.61  thf('46', plain,
% 0.40/0.61      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.40/0.61         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.61      inference('split', [status(esa)], ['42'])).
% 0.40/0.61  thf('47', plain,
% 0.40/0.61      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.40/0.61         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.61      inference('simplify', [status(thm)], ['47'])).
% 0.40/0.61  thf('49', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.61  thf('50', plain,
% 0.40/0.61      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.40/0.61         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['48', '49'])).
% 0.40/0.61  thf('51', plain,
% 0.40/0.61      (![X15 : $i, X16 : $i]:
% 0.40/0.61         (((k3_tarski @ (k2_tarski @ X16 @ X15)) = (X15))
% 0.40/0.61          | ~ (r1_tarski @ X16 @ X15))),
% 0.40/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf('52', plain,
% 0.40/0.61      ((![X0 : $i]: ((k3_tarski @ (k2_tarski @ sk_B_1 @ X0)) = (X0)))
% 0.40/0.61         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.61  thf('53', plain,
% 0.40/0.61      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 0.40/0.61         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['44', '52'])).
% 0.40/0.61  thf('54', plain,
% 0.40/0.61      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('55', plain,
% 0.40/0.61      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.40/0.61         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.40/0.61      inference('split', [status(esa)], ['54'])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.61      inference('split', [status(esa)], ['54'])).
% 0.40/0.61  thf('57', plain,
% 0.40/0.61      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('58', plain,
% 0.40/0.61      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.40/0.61       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('split', [status(esa)], ['57'])).
% 0.40/0.61  thf('59', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.61      inference('simplify', [status(thm)], ['47'])).
% 0.40/0.61  thf('60', plain,
% 0.40/0.61      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.61      inference('split', [status(esa)], ['54'])).
% 0.40/0.61  thf('61', plain,
% 0.40/0.61      ((((sk_B_1) != (sk_B_1)))
% 0.40/0.61         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.40/0.61             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['59', '60'])).
% 0.40/0.61  thf('62', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['61'])).
% 0.40/0.61  thf('63', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['56', '58', '62'])).
% 0.40/0.61  thf('64', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['55', '63'])).
% 0.40/0.61  thf('65', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['53', '64'])).
% 0.40/0.61  thf('66', plain,
% 0.40/0.61      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('split', [status(esa)], ['42'])).
% 0.40/0.61  thf('67', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['65', '66'])).
% 0.40/0.61  thf('68', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['43', '67'])).
% 0.40/0.61  thf('69', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['41', '68'])).
% 0.40/0.61  thf(d1_tarski, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.61  thf('70', plain,
% 0.40/0.61      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X29 @ X28)
% 0.40/0.61          | ((X29) = (X26))
% 0.40/0.61          | ((X28) != (k1_tarski @ X26)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.61  thf('71', plain,
% 0.40/0.61      (![X26 : $i, X29 : $i]:
% 0.40/0.61         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['70'])).
% 0.40/0.61  thf('72', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['69', '71'])).
% 0.40/0.61  thf('73', plain,
% 0.40/0.61      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.40/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.61  thf(l1_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.40/0.61  thf('74', plain,
% 0.40/0.61      (![X37 : $i, X39 : $i]:
% 0.40/0.61         ((r1_tarski @ (k1_tarski @ X37) @ X39) | ~ (r2_hidden @ X37 @ X39))),
% 0.40/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.61  thf('75', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.40/0.61  thf('76', plain,
% 0.40/0.61      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['72', '75'])).
% 0.40/0.61  thf('77', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['43', '67'])).
% 0.40/0.61  thf('78', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.40/0.61  thf('79', plain,
% 0.40/0.61      (((r1_tarski @ sk_B_1 @ sk_C_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['33', '78'])).
% 0.40/0.61  thf('80', plain,
% 0.40/0.61      (![X15 : $i, X16 : $i]:
% 0.40/0.61         (((k3_tarski @ (k2_tarski @ X16 @ X15)) = (X15))
% 0.40/0.61          | ~ (r1_tarski @ X16 @ X15))),
% 0.40/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf('81', plain,
% 0.40/0.61      ((((sk_B_1) = (k1_xboole_0))
% 0.40/0.61        | ((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (sk_C_1)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['79', '80'])).
% 0.40/0.61  thf('82', plain,
% 0.40/0.61      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['26', '81'])).
% 0.40/0.61  thf('83', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['55', '63'])).
% 0.40/0.61  thf('84', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 0.40/0.61  thf('85', plain,
% 0.40/0.61      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ sk_B_1 @ X0)) = (X0))),
% 0.40/0.61      inference('demod', [status(thm)], ['25', '84'])).
% 0.40/0.61  thf('86', plain, (((k1_tarski @ sk_A) = (sk_C_1))),
% 0.40/0.61      inference('demod', [status(thm)], ['2', '85'])).
% 0.40/0.61  thf('87', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['55', '63'])).
% 0.40/0.61  thf('88', plain, ($false),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
