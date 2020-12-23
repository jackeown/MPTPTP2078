%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CNscvLsMXb

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:17 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 569 expanded)
%              Number of leaves         :   27 ( 167 expanded)
%              Depth                    :   28
%              Number of atoms          :  828 (5904 expanded)
%              Number of equality atoms :  144 (1169 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('12',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( X30 = X27 )
      | ( X29
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('22',plain,(
    ! [X60: $i,X62: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X60 ) @ X62 )
      | ~ ( r2_hidden @ X60 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','35'])).

thf('37',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('45',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('46',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','47'])).

thf('49',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( k1_tarski @ sk_A )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( k1_tarski @ sk_A )
        = ( k2_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('54',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('60',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('63',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('64',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['59','61','65'])).

thf('67',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['58','66'])).

thf('68',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['56','67'])).

thf('69',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('70',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','70'])).

thf('72',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['36','71'])).

thf('73',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('74',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_2 )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( ( sk_B @ sk_C_2 )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('79',plain,(
    ! [X60: $i,X62: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X60 ) @ X62 )
      | ~ ( r2_hidden @ X60 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['38','70'])).

thf('83',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('87',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X0 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 )
    | ( ( k2_xboole_0 @ sk_C_2 @ sk_B_1 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('92',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['58','66'])).

thf('95',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['83','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','96'])).

thf('98',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['0','97'])).

thf('99',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['58','66'])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CNscvLsMXb
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 438 iterations in 0.141s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(t43_zfmisc_1, conjecture,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.41/0.60          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.41/0.60          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.41/0.60          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.60        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.41/0.60             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.41/0.60             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.41/0.60             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.41/0.60  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(commutativity_k2_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X25 : $i, X26 : $i]:
% 0.41/0.60         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.41/0.60  thf(l51_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X63 : $i, X64 : $i]:
% 0.41/0.60         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.41/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X63 : $i, X64 : $i]:
% 0.41/0.60         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.41/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf(t1_boole, axiom,
% 0.41/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.60  thf('6', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.41/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.60  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf(t7_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.41/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.41/0.60  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t7_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.60  thf('12', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf(d3_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X2 @ X3)
% 0.41/0.60          | (r2_hidden @ X2 @ X4)
% 0.41/0.60          | ~ (r1_tarski @ X3 @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0))
% 0.41/0.60        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '14'])).
% 0.41/0.60  thf(d1_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X30 @ X29)
% 0.41/0.60          | ((X30) = (X27))
% 0.41/0.60          | ((X29) != (k1_tarski @ X27)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X27 : $i, X30 : $i]:
% 0.41/0.60         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.41/0.60  thf('18', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B @ sk_B_1) = (sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '17'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (((r2_hidden @ sk_A @ sk_B_1)
% 0.41/0.60        | ((sk_B_1) = (k1_xboole_0))
% 0.41/0.60        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.41/0.60      inference('simplify', [status(thm)], ['20'])).
% 0.41/0.60  thf(l1_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X60 : $i, X62 : $i]:
% 0.41/0.60         ((r1_tarski @ (k1_tarski @ X60) @ X62) | ~ (r2_hidden @ X60 @ X62))),
% 0.41/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf(d10_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X9 : $i, X11 : $i]:
% 0.41/0.60         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.41/0.60        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['23', '26'])).
% 0.41/0.60  thf('28', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('32', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['28', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (((r1_tarski @ sk_C_2 @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['27', '32'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X2 @ X3)
% 0.41/0.60          | (r2_hidden @ X2 @ X4)
% 0.41/0.60          | ~ (r1_tarski @ X3 @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((sk_B_1) = (k1_xboole_0))
% 0.41/0.60          | (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      ((((sk_C_2) = (k1_xboole_0))
% 0.41/0.60        | (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)
% 0.41/0.60        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['8', '35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.41/0.60      inference('split', [status(esa)], ['37'])).
% 0.41/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.41/0.60  thf('39', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.41/0.60  thf(t100_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ X12 @ X13)
% 0.41/0.60           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf(t92_xboole_1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.60  thf('42', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.60  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['23', '26'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.41/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('split', [status(esa)], ['37'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.41/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      ((![X0 : $i]: ((sk_B_1) = (k4_xboole_0 @ X0 @ X0)))
% 0.41/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['43', '47'])).
% 0.41/0.60  thf('49', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      ((![X0 : $i]:
% 0.41/0.60          ((k1_tarski @ sk_A)
% 0.41/0.60            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_C_2)))
% 0.41/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['48', '49'])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      ((![X0 : $i]:
% 0.41/0.60          ((k1_tarski @ sk_A)
% 0.41/0.60            = (k2_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ X0 @ X0))))
% 0.41/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('sup+', [status(thm)], ['50', '51'])).
% 0.41/0.60  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('54', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.41/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['53', '54'])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      ((((k1_tarski @ sk_A) = (sk_C_2)))
% 0.41/0.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['52', '55'])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.41/0.60         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('split', [status(esa)], ['57'])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.60      inference('split', [status(esa)], ['57'])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.41/0.60       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['60'])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.41/0.60      inference('split', [status(esa)], ['57'])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      ((((sk_B_1) != (sk_B_1)))
% 0.41/0.60         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.41/0.60             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['64'])).
% 0.41/0.60  thf('66', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['59', '61', '65'])).
% 0.41/0.60  thf('67', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['58', '66'])).
% 0.41/0.60  thf('68', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['56', '67'])).
% 0.41/0.60  thf('69', plain,
% 0.41/0.60      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('split', [status(esa)], ['37'])).
% 0.41/0.60  thf('70', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.41/0.60  thf('71', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['38', '70'])).
% 0.41/0.60  thf('72', plain,
% 0.41/0.60      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['36', '71'])).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['23', '26'])).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      (![X27 : $i, X30 : $i]:
% 0.41/0.60         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.41/0.60  thf('75', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.60          | ((sk_B_1) = (k1_xboole_0))
% 0.41/0.60          | ((X0) = (sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['73', '74'])).
% 0.41/0.60  thf('76', plain,
% 0.41/0.60      ((((sk_B_1) = (k1_xboole_0))
% 0.41/0.60        | ((sk_B @ sk_C_2) = (sk_A))
% 0.41/0.60        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['72', '75'])).
% 0.41/0.60  thf('77', plain, ((((sk_B @ sk_C_2) = (sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['76'])).
% 0.41/0.60  thf('78', plain,
% 0.41/0.60      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.41/0.60  thf('79', plain,
% 0.41/0.60      (![X60 : $i, X62 : $i]:
% 0.41/0.60         ((r1_tarski @ (k1_tarski @ X60) @ X62) | ~ (r2_hidden @ X60 @ X62))),
% 0.41/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.41/0.60  thf('80', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.41/0.60  thf('81', plain,
% 0.41/0.60      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2)
% 0.41/0.60        | ((sk_B_1) = (k1_xboole_0))
% 0.41/0.60        | ((sk_C_2) = (k1_xboole_0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['77', '80'])).
% 0.41/0.60  thf('82', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['38', '70'])).
% 0.41/0.60  thf('83', plain,
% 0.41/0.60      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2) | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.41/0.60  thf('84', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('85', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf('86', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.60  thf('87', plain,
% 0.41/0.60      (![X9 : $i, X11 : $i]:
% 0.41/0.60         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('88', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.41/0.60          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['86', '87'])).
% 0.41/0.60  thf('89', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.41/0.60          | ((k2_xboole_0 @ X0 @ X1) = (X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['85', '88'])).
% 0.41/0.60  thf('90', plain,
% 0.41/0.60      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2)
% 0.41/0.60        | ((k2_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_C_2)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['84', '89'])).
% 0.41/0.60  thf('91', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf('92', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('93', plain,
% 0.41/0.60      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2)
% 0.41/0.60        | ((k1_tarski @ sk_A) = (sk_C_2)))),
% 0.41/0.60      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.41/0.60  thf('94', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['58', '66'])).
% 0.41/0.60  thf('95', plain, (~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2)),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.41/0.60  thf('96', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.41/0.60      inference('clc', [status(thm)], ['83', '95'])).
% 0.41/0.60  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['7', '96'])).
% 0.41/0.60  thf('98', plain, (((k1_tarski @ sk_A) = (sk_C_2))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '97'])).
% 0.41/0.60  thf('99', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['58', '66'])).
% 0.41/0.60  thf('100', plain, ($false),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['98', '99'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
