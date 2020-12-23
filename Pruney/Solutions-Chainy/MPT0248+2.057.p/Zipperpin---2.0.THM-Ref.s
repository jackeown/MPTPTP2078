%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VzOd766JKa

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:26 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 466 expanded)
%              Number of leaves         :   30 ( 146 expanded)
%              Depth                    :   26
%              Number of atoms          :  741 (4466 expanded)
%              Number of equality atoms :   97 ( 757 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X63: $i,X64: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X63 ) @ X64 )
      | ( r2_hidden @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X25: $i] :
      ( ( k3_xboole_0 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ k1_xboole_0 )
      = X29 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X27 @ X28 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( k2_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
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

thf('20',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X60: $i,X62: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X60 ) @ X62 )
      | ~ ( r2_hidden @ X60 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X63: $i,X64: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X63 ) @ X64 )
      | ( r2_hidden @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X60: $i,X62: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X60 ) @ X62 )
      | ~ ( r2_hidden @ X60 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['46','59'])).

thf('61',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('64',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('67',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('68',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['63','65','71'])).

thf('73',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['62','72'])).

thf('74',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['60','73'])).

thf('75',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('76',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('81',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','81'])).

thf('83',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['60','73'])).

thf('84',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('85',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('88',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X27 @ X28 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('89',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['0','86','91'])).

thf('93',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['62','72'])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VzOd766JKa
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:01:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.82/2.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.82/2.04  % Solved by: fo/fo7.sh
% 1.82/2.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.82/2.04  % done 5005 iterations in 1.586s
% 1.82/2.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.82/2.04  % SZS output start Refutation
% 1.82/2.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.82/2.04  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.82/2.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.82/2.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.82/2.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.82/2.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.82/2.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.82/2.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.82/2.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.82/2.04  thf(sk_B_type, type, sk_B: $i > $i).
% 1.82/2.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.82/2.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.82/2.04  thf(sk_A_type, type, sk_A: $i).
% 1.82/2.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.82/2.04  thf(t43_zfmisc_1, conjecture,
% 1.82/2.04    (![A:$i,B:$i,C:$i]:
% 1.82/2.04     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.82/2.04          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.82/2.04          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.82/2.04          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.82/2.04  thf(zf_stmt_0, negated_conjecture,
% 1.82/2.04    (~( ![A:$i,B:$i,C:$i]:
% 1.82/2.04        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.82/2.04             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.82/2.04             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.82/2.04             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.82/2.04    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.82/2.04  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.82/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.04  thf(d1_xboole_0, axiom,
% 1.82/2.04    (![A:$i]:
% 1.82/2.04     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.82/2.04  thf('1', plain,
% 1.82/2.04      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.82/2.04      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.82/2.04  thf(l27_zfmisc_1, axiom,
% 1.82/2.04    (![A:$i,B:$i]:
% 1.82/2.04     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.82/2.04  thf('2', plain,
% 1.82/2.04      (![X63 : $i, X64 : $i]:
% 1.82/2.04         ((r1_xboole_0 @ (k1_tarski @ X63) @ X64) | (r2_hidden @ X63 @ X64))),
% 1.82/2.04      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.82/2.04  thf('3', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.82/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.04  thf(t2_boole, axiom,
% 1.82/2.04    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.82/2.04  thf('4', plain,
% 1.82/2.04      (![X25 : $i]: ((k3_xboole_0 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 1.82/2.04      inference('cnf', [status(esa)], [t2_boole])).
% 1.82/2.04  thf(t100_xboole_1, axiom,
% 1.82/2.04    (![A:$i,B:$i]:
% 1.82/2.04     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.82/2.04  thf('5', plain,
% 1.82/2.04      (![X13 : $i, X14 : $i]:
% 1.82/2.04         ((k4_xboole_0 @ X13 @ X14)
% 1.82/2.04           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.82/2.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.82/2.04  thf('6', plain,
% 1.82/2.04      (![X0 : $i]:
% 1.82/2.04         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.82/2.04      inference('sup+', [status(thm)], ['4', '5'])).
% 1.82/2.04  thf(t5_boole, axiom,
% 1.82/2.04    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.82/2.04  thf('7', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ k1_xboole_0) = (X29))),
% 1.82/2.04      inference('cnf', [status(esa)], [t5_boole])).
% 1.82/2.04  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.82/2.04      inference('demod', [status(thm)], ['6', '7'])).
% 1.82/2.04  thf(t36_xboole_1, axiom,
% 1.82/2.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.82/2.04  thf('9', plain,
% 1.82/2.04      (![X27 : $i, X28 : $i]: (r1_tarski @ (k4_xboole_0 @ X27 @ X28) @ X27)),
% 1.82/2.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.82/2.04  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.82/2.04      inference('sup+', [status(thm)], ['8', '9'])).
% 1.82/2.04  thf(t10_xboole_1, axiom,
% 1.82/2.04    (![A:$i,B:$i,C:$i]:
% 1.82/2.04     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.82/2.04  thf('11', plain,
% 1.82/2.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.82/2.04         (~ (r1_tarski @ X15 @ X16)
% 1.82/2.04          | (r1_tarski @ X15 @ (k2_xboole_0 @ X17 @ X16)))),
% 1.82/2.04      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.82/2.04  thf('12', plain,
% 1.82/2.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.82/2.04      inference('sup-', [status(thm)], ['10', '11'])).
% 1.82/2.04  thf('13', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 1.82/2.04      inference('sup+', [status(thm)], ['3', '12'])).
% 1.82/2.04  thf(t12_xboole_1, axiom,
% 1.82/2.04    (![A:$i,B:$i]:
% 1.82/2.04     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.82/2.04  thf('14', plain,
% 1.82/2.04      (![X18 : $i, X19 : $i]:
% 1.82/2.04         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 1.82/2.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.82/2.04  thf('15', plain,
% 1.82/2.04      (((k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.82/2.04      inference('sup-', [status(thm)], ['13', '14'])).
% 1.82/2.04  thf(t7_xboole_1, axiom,
% 1.82/2.04    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.82/2.04  thf('16', plain,
% 1.82/2.04      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 1.82/2.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.82/2.04  thf(t28_xboole_1, axiom,
% 1.82/2.04    (![A:$i,B:$i]:
% 1.82/2.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.82/2.04  thf('17', plain,
% 1.82/2.04      (![X23 : $i, X24 : $i]:
% 1.82/2.04         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 1.82/2.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.82/2.04  thf('18', plain,
% 1.82/2.04      (![X0 : $i, X1 : $i]:
% 1.82/2.04         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['16', '17'])).
% 1.82/2.04  thf(commutativity_k3_xboole_0, axiom,
% 1.82/2.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.82/2.04  thf('19', plain,
% 1.82/2.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.82/2.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.82/2.04  thf(t4_xboole_0, axiom,
% 1.82/2.04    (![A:$i,B:$i]:
% 1.82/2.04     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.82/2.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.82/2.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.82/2.04            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.82/2.04  thf('20', plain,
% 1.82/2.04      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.82/2.04         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 1.82/2.04          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.82/2.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.82/2.04  thf('21', plain,
% 1.82/2.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.04         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.82/2.04          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['19', '20'])).
% 1.82/2.04  thf('22', plain,
% 1.82/2.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.04         (~ (r2_hidden @ X2 @ X0)
% 1.82/2.04          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.82/2.04      inference('sup-', [status(thm)], ['18', '21'])).
% 1.82/2.04  thf('23', plain,
% 1.82/2.04      (![X0 : $i]:
% 1.82/2.04         (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1)
% 1.82/2.04          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['15', '22'])).
% 1.82/2.04  thf('24', plain,
% 1.82/2.04      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['2', '23'])).
% 1.82/2.04  thf('25', plain, (((v1_xboole_0 @ sk_C_1) | (r2_hidden @ sk_A @ sk_C_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['1', '24'])).
% 1.82/2.04  thf(l1_zfmisc_1, axiom,
% 1.82/2.04    (![A:$i,B:$i]:
% 1.82/2.04     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.82/2.04  thf('26', plain,
% 1.82/2.04      (![X60 : $i, X62 : $i]:
% 1.82/2.04         ((r1_tarski @ (k1_tarski @ X60) @ X62) | ~ (r2_hidden @ X60 @ X62))),
% 1.82/2.04      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.82/2.04  thf('27', plain,
% 1.82/2.04      (((v1_xboole_0 @ sk_C_1) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['25', '26'])).
% 1.82/2.04  thf('28', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.82/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.04  thf('29', plain,
% 1.82/2.04      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 1.82/2.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.82/2.04  thf('30', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.82/2.04      inference('sup+', [status(thm)], ['28', '29'])).
% 1.82/2.04  thf(t1_xboole_1, axiom,
% 1.82/2.04    (![A:$i,B:$i,C:$i]:
% 1.82/2.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.82/2.04       ( r1_tarski @ A @ C ) ))).
% 1.82/2.04  thf('31', plain,
% 1.82/2.04      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.82/2.04         (~ (r1_tarski @ X20 @ X21)
% 1.82/2.04          | ~ (r1_tarski @ X21 @ X22)
% 1.82/2.04          | (r1_tarski @ X20 @ X22))),
% 1.82/2.04      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.82/2.04  thf('32', plain,
% 1.82/2.04      (![X0 : $i]:
% 1.82/2.04         ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 1.82/2.04      inference('sup-', [status(thm)], ['30', '31'])).
% 1.82/2.04  thf('33', plain, (((v1_xboole_0 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['27', '32'])).
% 1.82/2.04  thf('34', plain,
% 1.82/2.04      (![X18 : $i, X19 : $i]:
% 1.82/2.04         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 1.82/2.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.82/2.04  thf('35', plain,
% 1.82/2.04      (((v1_xboole_0 @ sk_C_1) | ((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1)))),
% 1.82/2.04      inference('sup-', [status(thm)], ['33', '34'])).
% 1.82/2.04  thf('36', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.82/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.04  thf('37', plain,
% 1.82/2.04      ((((k1_tarski @ sk_A) = (sk_C_1)) | (v1_xboole_0 @ sk_C_1))),
% 1.82/2.04      inference('sup+', [status(thm)], ['35', '36'])).
% 1.82/2.04  thf('38', plain,
% 1.82/2.04      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.82/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.04  thf('39', plain,
% 1.82/2.04      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.82/2.04         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.82/2.04      inference('split', [status(esa)], ['38'])).
% 1.82/2.04  thf('40', plain,
% 1.82/2.04      (((((sk_C_1) != (sk_C_1)) | (v1_xboole_0 @ sk_C_1)))
% 1.82/2.04         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.82/2.04      inference('sup-', [status(thm)], ['37', '39'])).
% 1.82/2.04  thf('41', plain,
% 1.82/2.04      (((v1_xboole_0 @ sk_C_1)) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.82/2.04      inference('simplify', [status(thm)], ['40'])).
% 1.82/2.04  thf(l13_xboole_0, axiom,
% 1.82/2.04    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.82/2.04  thf('42', plain,
% 1.82/2.04      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.82/2.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.82/2.04  thf('43', plain,
% 1.82/2.04      ((((sk_C_1) = (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.82/2.04      inference('sup-', [status(thm)], ['41', '42'])).
% 1.82/2.04  thf('44', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.82/2.04      inference('sup+', [status(thm)], ['28', '29'])).
% 1.82/2.04  thf('45', plain,
% 1.82/2.04      (![X23 : $i, X24 : $i]:
% 1.82/2.04         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 1.82/2.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.82/2.04  thf('46', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['44', '45'])).
% 1.82/2.04  thf('47', plain,
% 1.82/2.04      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.82/2.04      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.82/2.04  thf('48', plain,
% 1.82/2.04      (![X63 : $i, X64 : $i]:
% 1.82/2.04         ((r1_xboole_0 @ (k1_tarski @ X63) @ X64) | (r2_hidden @ X63 @ X64))),
% 1.82/2.04      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.82/2.04  thf('49', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['44', '45'])).
% 1.82/2.04  thf('50', plain,
% 1.82/2.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.04         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.82/2.04          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['19', '20'])).
% 1.82/2.04  thf('51', plain,
% 1.82/2.04      (![X0 : $i]:
% 1.82/2.04         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.82/2.04          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['49', '50'])).
% 1.82/2.04  thf('52', plain,
% 1.82/2.04      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['48', '51'])).
% 1.82/2.04  thf('53', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['47', '52'])).
% 1.82/2.04  thf('54', plain,
% 1.82/2.04      (![X60 : $i, X62 : $i]:
% 1.82/2.04         ((r1_tarski @ (k1_tarski @ X60) @ X62) | ~ (r2_hidden @ X60 @ X62))),
% 1.82/2.04      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.82/2.04  thf('55', plain,
% 1.82/2.04      (((v1_xboole_0 @ sk_B_1) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.82/2.04      inference('sup-', [status(thm)], ['53', '54'])).
% 1.82/2.04  thf('56', plain,
% 1.82/2.04      (![X23 : $i, X24 : $i]:
% 1.82/2.04         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 1.82/2.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.82/2.04  thf('57', plain,
% 1.82/2.04      (((v1_xboole_0 @ sk_B_1)
% 1.82/2.04        | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 1.82/2.04      inference('sup-', [status(thm)], ['55', '56'])).
% 1.82/2.04  thf('58', plain,
% 1.82/2.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.82/2.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.82/2.04  thf('59', plain,
% 1.82/2.04      (((v1_xboole_0 @ sk_B_1)
% 1.82/2.04        | ((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 1.82/2.04      inference('demod', [status(thm)], ['57', '58'])).
% 1.82/2.04  thf('60', plain,
% 1.82/2.04      ((((sk_B_1) = (k1_tarski @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 1.82/2.04      inference('sup+', [status(thm)], ['46', '59'])).
% 1.82/2.04  thf('61', plain,
% 1.82/2.04      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 1.82/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.04  thf('62', plain,
% 1.82/2.04      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.82/2.04         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.82/2.04      inference('split', [status(esa)], ['61'])).
% 1.82/2.04  thf('63', plain,
% 1.82/2.04      (~ (((sk_B_1) = (k1_tarski @ sk_A))) | ~ (((sk_C_1) = (k1_xboole_0)))),
% 1.82/2.04      inference('split', [status(esa)], ['61'])).
% 1.82/2.04  thf('64', plain,
% 1.82/2.04      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.82/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.04  thf('65', plain,
% 1.82/2.04      (~ (((sk_B_1) = (k1_tarski @ sk_A))) | 
% 1.82/2.04       ~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.82/2.04      inference('split', [status(esa)], ['64'])).
% 1.82/2.04  thf('66', plain,
% 1.82/2.04      (((v1_xboole_0 @ sk_C_1)) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.82/2.04      inference('simplify', [status(thm)], ['40'])).
% 1.82/2.04  thf('67', plain,
% 1.82/2.04      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.82/2.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.82/2.04  thf('68', plain,
% 1.82/2.04      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.82/2.04      inference('split', [status(esa)], ['61'])).
% 1.82/2.04  thf('69', plain,
% 1.82/2.04      ((![X0 : $i]: (((sk_C_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.82/2.04         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.82/2.04      inference('sup-', [status(thm)], ['67', '68'])).
% 1.82/2.04  thf('70', plain,
% 1.82/2.04      ((~ (v1_xboole_0 @ sk_C_1)) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.82/2.04      inference('simplify', [status(thm)], ['69'])).
% 1.82/2.04  thf('71', plain,
% 1.82/2.04      ((((sk_C_1) = (k1_xboole_0))) | (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.82/2.04      inference('sup-', [status(thm)], ['66', '70'])).
% 1.82/2.04  thf('72', plain, (~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.82/2.04      inference('sat_resolution*', [status(thm)], ['63', '65', '71'])).
% 1.82/2.04  thf('73', plain, (((sk_B_1) != (k1_tarski @ sk_A))),
% 1.82/2.04      inference('simpl_trail', [status(thm)], ['62', '72'])).
% 1.82/2.04  thf('74', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.82/2.04      inference('simplify_reflect-', [status(thm)], ['60', '73'])).
% 1.82/2.04  thf('75', plain,
% 1.82/2.04      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.82/2.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.82/2.04  thf('76', plain,
% 1.82/2.04      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.82/2.04      inference('split', [status(esa)], ['38'])).
% 1.82/2.04  thf('77', plain,
% 1.82/2.04      ((![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.82/2.04         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.82/2.04      inference('sup-', [status(thm)], ['75', '76'])).
% 1.82/2.04  thf('78', plain,
% 1.82/2.04      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.82/2.04      inference('simplify', [status(thm)], ['77'])).
% 1.82/2.04  thf('79', plain, ((((sk_B_1) = (k1_xboole_0)))),
% 1.82/2.04      inference('sup-', [status(thm)], ['74', '78'])).
% 1.82/2.04  thf('80', plain,
% 1.82/2.04      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.82/2.04      inference('split', [status(esa)], ['38'])).
% 1.82/2.04  thf('81', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.82/2.04      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 1.82/2.04  thf('82', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.82/2.04      inference('simpl_trail', [status(thm)], ['43', '81'])).
% 1.82/2.04  thf('83', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.82/2.04      inference('simplify_reflect-', [status(thm)], ['60', '73'])).
% 1.82/2.04  thf('84', plain,
% 1.82/2.04      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.82/2.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.82/2.04  thf('85', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.82/2.04      inference('sup-', [status(thm)], ['83', '84'])).
% 1.82/2.04  thf('86', plain, (((sk_B_1) = (sk_C_1))),
% 1.82/2.04      inference('sup+', [status(thm)], ['82', '85'])).
% 1.82/2.04  thf('87', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.82/2.04      inference('demod', [status(thm)], ['6', '7'])).
% 1.82/2.04  thf('88', plain,
% 1.82/2.04      (![X27 : $i, X28 : $i]: (r1_tarski @ (k4_xboole_0 @ X27 @ X28) @ X27)),
% 1.82/2.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.82/2.04  thf('89', plain,
% 1.82/2.04      (![X18 : $i, X19 : $i]:
% 1.82/2.04         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 1.82/2.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.82/2.04  thf('90', plain,
% 1.82/2.04      (![X0 : $i, X1 : $i]:
% 1.82/2.04         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.82/2.04      inference('sup-', [status(thm)], ['88', '89'])).
% 1.82/2.04  thf('91', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.82/2.04      inference('sup+', [status(thm)], ['87', '90'])).
% 1.82/2.04  thf('92', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 1.82/2.04      inference('demod', [status(thm)], ['0', '86', '91'])).
% 1.82/2.04  thf('93', plain, (((sk_B_1) != (k1_tarski @ sk_A))),
% 1.82/2.04      inference('simpl_trail', [status(thm)], ['62', '72'])).
% 1.82/2.04  thf('94', plain, ($false),
% 1.82/2.04      inference('simplify_reflect-', [status(thm)], ['92', '93'])).
% 1.82/2.04  
% 1.82/2.04  % SZS output end Refutation
% 1.82/2.04  
% 1.82/2.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
