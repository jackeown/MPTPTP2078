%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WhMd7uog6s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:27 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  168 (2143 expanded)
%              Number of leaves         :   33 ( 636 expanded)
%              Depth                    :   24
%              Number of atoms          : 1097 (22465 expanded)
%              Number of equality atoms :  162 (4063 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('19',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['14','20'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['14','20'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('40',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('43',plain,(
    ! [X62: $i,X63: $i] :
      ( ( X63
        = ( k1_tarski @ X62 ) )
      | ( X63 = k1_xboole_0 )
      | ~ ( r1_tarski @ X63 @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('44',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('50',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['39','41','51'])).

thf('53',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['38','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['36','53'])).

thf('55',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['29','54'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('56',plain,(
    ! [X59: $i,X61: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X59 ) @ X61 )
      | ~ ( r2_hidden @ X59 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('57',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['29','54'])).

thf('59',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('60',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('63',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( X29 = X26 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('64',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['57','65'])).

thf('67',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','66'])).

thf('68',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','67'])).

thf('69',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['72','79'])).

thf('81',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','66'])).

thf('82',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('83',plain,(
    ! [X62: $i,X63: $i] :
      ( ( X63
        = ( k1_tarski @ X62 ) )
      | ( X63 = k1_xboole_0 )
      | ~ ( r1_tarski @ X63 @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B_1 @ X0 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','66'])).

thf('87',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','66'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ( ( k3_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['72','79'])).

thf('90',plain,
    ( ( k1_xboole_0 = sk_C_2 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['45'])).

thf('92',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('93',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('94',plain,(
    ! [X59: $i,X61: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X59 ) @ X61 )
      | ~ ( r2_hidden @ X59 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('97',plain,(
    ! [X63: $i,X64: $i] :
      ( ( r1_tarski @ X63 @ ( k1_tarski @ X64 ) )
      | ( X63 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('98',plain,(
    ! [X64: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X64 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ ( k1_tarski @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['96','98'])).

thf('100',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_B_1 )
        | ( ( k1_tarski @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['36','53'])).

thf('104',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('106',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('107',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = ( sk_B @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('112',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','111'])).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('114',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r2_hidden @ X59 @ X60 )
      | ~ ( r1_tarski @ ( k1_tarski @ X59 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['112','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('119',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('121',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','111'])).

thf('123',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','121','122'])).

thf('124',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf('126',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['124','125'])).

thf('127',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['91','126'])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['90','127'])).

thf('129',plain,(
    sk_C_2 = sk_B_1 ),
    inference('sup+',[status(thm)],['80','128'])).

thf('130',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['38','52'])).

thf('131',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','66'])).

thf('132',plain,(
    sk_C_2 != sk_B_1 ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['129','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WhMd7uog6s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.99  % Solved by: fo/fo7.sh
% 0.74/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.99  % done 1148 iterations in 0.510s
% 0.74/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.99  % SZS output start Refutation
% 0.74/0.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.74/0.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.74/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.74/0.99  thf(sk_B_type, type, sk_B: $i > $i).
% 0.74/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.74/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.74/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.99  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.74/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.99  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.74/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.99  thf(t43_zfmisc_1, conjecture,
% 0.74/0.99    (![A:$i,B:$i,C:$i]:
% 0.74/0.99     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.74/0.99          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.74/0.99          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.74/0.99          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.74/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.99    (~( ![A:$i,B:$i,C:$i]:
% 0.74/0.99        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.74/0.99             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.74/0.99             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.74/0.99             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.74/0.99    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.74/0.99  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.74/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.99  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.74/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.99  thf(t7_xboole_1, axiom,
% 0.74/0.99    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.74/0.99  thf('2', plain,
% 0.74/0.99      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.74/0.99      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.74/0.99  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.74/0.99      inference('sup+', [status(thm)], ['1', '2'])).
% 0.74/0.99  thf(d10_xboole_0, axiom,
% 0.74/0.99    (![A:$i,B:$i]:
% 0.74/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/0.99  thf('4', plain,
% 0.74/0.99      (![X11 : $i, X13 : $i]:
% 0.74/0.99         (((X11) = (X13))
% 0.74/0.99          | ~ (r1_tarski @ X13 @ X11)
% 0.74/0.99          | ~ (r1_tarski @ X11 @ X13))),
% 0.74/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.99  thf('5', plain,
% 0.74/0.99      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.74/0.99        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.74/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.99  thf('6', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.74/0.99      inference('sup+', [status(thm)], ['1', '2'])).
% 0.74/0.99  thf(t12_xboole_1, axiom,
% 0.74/0.99    (![A:$i,B:$i]:
% 0.74/0.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.74/0.99  thf('7', plain,
% 0.74/0.99      (![X14 : $i, X15 : $i]:
% 0.74/0.99         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.74/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.74/0.99  thf('8', plain,
% 0.74/0.99      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.74/0.99      inference('sup-', [status(thm)], ['6', '7'])).
% 0.74/0.99  thf(t95_xboole_1, axiom,
% 0.74/0.99    (![A:$i,B:$i]:
% 0.74/0.99     ( ( k3_xboole_0 @ A @ B ) =
% 0.74/0.99       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.74/0.99  thf('9', plain,
% 0.74/0.99      (![X24 : $i, X25 : $i]:
% 0.74/0.99         ((k3_xboole_0 @ X24 @ X25)
% 0.74/0.99           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.74/0.99              (k2_xboole_0 @ X24 @ X25)))),
% 0.74/0.99      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.74/0.99  thf(t91_xboole_1, axiom,
% 0.74/0.99    (![A:$i,B:$i,C:$i]:
% 0.74/0.99     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.74/0.99       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.74/0.99  thf('10', plain,
% 0.74/0.99      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.74/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.74/0.99           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.74/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.74/0.99  thf('11', plain,
% 0.74/0.99      (![X24 : $i, X25 : $i]:
% 0.74/0.99         ((k3_xboole_0 @ X24 @ X25)
% 0.74/0.99           = (k5_xboole_0 @ X24 @ 
% 0.74/0.99              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.74/0.99      inference('demod', [status(thm)], ['9', '10'])).
% 0.74/0.99  thf('12', plain,
% 0.74/0.99      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.74/0.99         = (k5_xboole_0 @ sk_B_1 @ 
% 0.74/0.99            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup+', [status(thm)], ['8', '11'])).
% 0.74/0.99  thf(t92_xboole_1, axiom,
% 0.74/0.99    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.74/0.99  thf('13', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.74/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.74/0.99  thf('14', plain,
% 0.74/0.99      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.74/0.99         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.74/0.99      inference('demod', [status(thm)], ['12', '13'])).
% 0.74/0.99  thf(idempotence_k2_xboole_0, axiom,
% 0.74/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.74/0.99  thf('15', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ X9) = (X9))),
% 0.74/0.99      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.74/0.99  thf('16', plain,
% 0.74/0.99      (![X24 : $i, X25 : $i]:
% 0.74/0.99         ((k3_xboole_0 @ X24 @ X25)
% 0.74/0.99           = (k5_xboole_0 @ X24 @ 
% 0.74/0.99              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.74/0.99      inference('demod', [status(thm)], ['9', '10'])).
% 0.74/0.99  thf('17', plain,
% 0.74/0.99      (![X0 : $i]:
% 0.74/0.99         ((k3_xboole_0 @ X0 @ X0)
% 0.74/0.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.74/0.99      inference('sup+', [status(thm)], ['15', '16'])).
% 0.74/0.99  thf(idempotence_k3_xboole_0, axiom,
% 0.74/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.74/0.99  thf('18', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.74/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.74/0.99  thf('19', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.74/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.74/0.99  thf('20', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/0.99      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.74/0.99  thf('21', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.74/0.99      inference('demod', [status(thm)], ['14', '20'])).
% 0.74/0.99  thf(d1_xboole_0, axiom,
% 0.74/0.99    (![A:$i]:
% 0.74/0.99     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.74/0.99  thf('22', plain,
% 0.74/0.99      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.74/0.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.99  thf(t17_xboole_1, axiom,
% 0.74/0.99    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.74/0.99  thf('23', plain,
% 0.74/0.99      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.74/0.99      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.74/0.99  thf(d3_tarski, axiom,
% 0.74/0.99    (![A:$i,B:$i]:
% 0.74/0.99     ( ( r1_tarski @ A @ B ) <=>
% 0.74/0.99       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.74/0.99  thf('24', plain,
% 0.74/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.74/0.99         (~ (r2_hidden @ X5 @ X6)
% 0.74/0.99          | (r2_hidden @ X5 @ X7)
% 0.74/0.99          | ~ (r1_tarski @ X6 @ X7))),
% 0.74/0.99      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.99  thf('25', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.99         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.74/0.99      inference('sup-', [status(thm)], ['23', '24'])).
% 0.74/0.99  thf('26', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i]:
% 0.74/0.99         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.74/0.99          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.74/0.99      inference('sup-', [status(thm)], ['22', '25'])).
% 0.74/0.99  thf('27', plain,
% 0.74/0.99      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)
% 0.74/0.99        | (v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup+', [status(thm)], ['21', '26'])).
% 0.74/0.99  thf('28', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.74/0.99      inference('demod', [status(thm)], ['14', '20'])).
% 0.74/0.99  thf('29', plain,
% 0.74/0.99      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1) | (v1_xboole_0 @ sk_B_1))),
% 0.74/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.74/0.99  thf('30', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.74/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.99  thf('31', plain,
% 0.74/0.99      (![X6 : $i, X8 : $i]:
% 0.74/0.99         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.74/0.99      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.99  thf('32', plain,
% 0.74/0.99      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.74/0.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.99  thf('33', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.99      inference('sup-', [status(thm)], ['31', '32'])).
% 0.74/0.99  thf('34', plain,
% 0.74/0.99      (![X14 : $i, X15 : $i]:
% 0.74/0.99         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.74/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.74/0.99  thf('35', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i]:
% 0.74/0.99         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.74/0.99      inference('sup-', [status(thm)], ['33', '34'])).
% 0.74/0.99  thf('36', plain,
% 0.74/0.99      ((((k1_tarski @ sk_A) = (sk_C_2)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.74/0.99      inference('sup+', [status(thm)], ['30', '35'])).
% 0.74/0.99  thf('37', plain,
% 0.74/0.99      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.74/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.99  thf('38', plain,
% 0.74/0.99      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.74/0.99         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('split', [status(esa)], ['37'])).
% 0.74/0.99  thf('39', plain,
% 0.74/0.99      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.74/0.99      inference('split', [status(esa)], ['37'])).
% 0.74/0.99  thf('40', plain,
% 0.74/0.99      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.74/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.99  thf('41', plain,
% 0.74/0.99      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.74/0.99       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.74/0.99      inference('split', [status(esa)], ['40'])).
% 0.74/0.99  thf('42', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.74/0.99      inference('sup+', [status(thm)], ['1', '2'])).
% 0.74/0.99  thf(l3_zfmisc_1, axiom,
% 0.74/0.99    (![A:$i,B:$i]:
% 0.74/0.99     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.74/0.99       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.74/0.99  thf('43', plain,
% 0.74/0.99      (![X62 : $i, X63 : $i]:
% 0.74/0.99         (((X63) = (k1_tarski @ X62))
% 0.74/0.99          | ((X63) = (k1_xboole_0))
% 0.74/0.99          | ~ (r1_tarski @ X63 @ (k1_tarski @ X62)))),
% 0.74/0.99      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.74/0.99  thf('44', plain,
% 0.74/0.99      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.74/0.99      inference('sup-', [status(thm)], ['42', '43'])).
% 0.74/0.99  thf('45', plain,
% 0.74/0.99      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.74/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.99  thf('46', plain,
% 0.74/0.99      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('split', [status(esa)], ['45'])).
% 0.74/0.99  thf('47', plain,
% 0.74/0.99      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup-', [status(thm)], ['44', '46'])).
% 0.74/0.99  thf('48', plain,
% 0.74/0.99      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('simplify', [status(thm)], ['47'])).
% 0.74/0.99  thf('49', plain,
% 0.74/0.99      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.74/0.99      inference('split', [status(esa)], ['37'])).
% 0.74/0.99  thf('50', plain,
% 0.74/0.99      ((((sk_B_1) != (sk_B_1)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.74/0.99             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup-', [status(thm)], ['48', '49'])).
% 0.74/0.99  thf('51', plain,
% 0.74/0.99      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.74/0.99      inference('simplify', [status(thm)], ['50'])).
% 0.74/0.99  thf('52', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.74/0.99      inference('sat_resolution*', [status(thm)], ['39', '41', '51'])).
% 0.74/0.99  thf('53', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.74/0.99      inference('simpl_trail', [status(thm)], ['38', '52'])).
% 0.74/0.99  thf('54', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.74/0.99      inference('simplify_reflect-', [status(thm)], ['36', '53'])).
% 0.74/0.99  thf('55', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.74/0.99      inference('clc', [status(thm)], ['29', '54'])).
% 0.74/0.99  thf(l1_zfmisc_1, axiom,
% 0.74/0.99    (![A:$i,B:$i]:
% 0.74/0.99     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.74/0.99  thf('56', plain,
% 0.74/0.99      (![X59 : $i, X61 : $i]:
% 0.74/0.99         ((r1_tarski @ (k1_tarski @ X59) @ X61) | ~ (r2_hidden @ X59 @ X61))),
% 0.74/0.99      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.74/0.99  thf('57', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 0.74/0.99      inference('sup-', [status(thm)], ['55', '56'])).
% 0.74/0.99  thf('58', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.74/0.99      inference('clc', [status(thm)], ['29', '54'])).
% 0.74/0.99  thf('59', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.74/0.99      inference('sup+', [status(thm)], ['1', '2'])).
% 0.74/0.99  thf('60', plain,
% 0.74/0.99      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.74/0.99         (~ (r2_hidden @ X5 @ X6)
% 0.74/0.99          | (r2_hidden @ X5 @ X7)
% 0.74/0.99          | ~ (r1_tarski @ X6 @ X7))),
% 0.74/0.99      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.99  thf('61', plain,
% 0.74/0.99      (![X0 : $i]:
% 0.74/0.99         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.74/0.99      inference('sup-', [status(thm)], ['59', '60'])).
% 0.74/0.99  thf('62', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.74/0.99      inference('sup-', [status(thm)], ['58', '61'])).
% 0.74/0.99  thf(d1_tarski, axiom,
% 0.74/0.99    (![A:$i,B:$i]:
% 0.74/0.99     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.74/0.99       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.74/0.99  thf('63', plain,
% 0.74/0.99      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.74/0.99         (~ (r2_hidden @ X29 @ X28)
% 0.74/0.99          | ((X29) = (X26))
% 0.74/0.99          | ((X28) != (k1_tarski @ X26)))),
% 0.74/0.99      inference('cnf', [status(esa)], [d1_tarski])).
% 0.74/0.99  thf('64', plain,
% 0.74/0.99      (![X26 : $i, X29 : $i]:
% 0.74/0.99         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 0.74/0.99      inference('simplify', [status(thm)], ['63'])).
% 0.74/0.99  thf('65', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.74/0.99      inference('sup-', [status(thm)], ['62', '64'])).
% 0.74/0.99  thf('66', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.74/0.99      inference('demod', [status(thm)], ['57', '65'])).
% 0.74/0.99  thf('67', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.74/0.99      inference('demod', [status(thm)], ['5', '66'])).
% 0.74/0.99  thf('68', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.74/0.99      inference('demod', [status(thm)], ['0', '67'])).
% 0.74/0.99  thf('69', plain,
% 0.74/0.99      (![X24 : $i, X25 : $i]:
% 0.74/0.99         ((k3_xboole_0 @ X24 @ X25)
% 0.74/0.99           = (k5_xboole_0 @ X24 @ 
% 0.74/0.99              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.74/0.99      inference('demod', [status(thm)], ['9', '10'])).
% 0.74/0.99  thf('70', plain,
% 0.74/0.99      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.74/0.99         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ sk_B_1)))),
% 0.74/0.99      inference('sup+', [status(thm)], ['68', '69'])).
% 0.74/0.99  thf(commutativity_k5_xboole_0, axiom,
% 0.74/0.99    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.74/0.99  thf('71', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.74/0.99      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.74/0.99  thf('72', plain,
% 0.74/0.99      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.74/0.99         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.74/0.99      inference('demod', [status(thm)], ['70', '71'])).
% 0.74/0.99  thf('73', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.74/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.74/0.99  thf('74', plain,
% 0.74/0.99      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.74/0.99         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.74/0.99           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.74/0.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.74/0.99  thf('75', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.74/0.99      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.74/0.99  thf('76', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.74/0.99           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.74/0.99      inference('sup+', [status(thm)], ['74', '75'])).
% 0.74/0.99  thf('77', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i]:
% 0.74/0.99         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.74/0.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.74/0.99      inference('sup+', [status(thm)], ['73', '76'])).
% 0.74/0.99  thf('78', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/0.99      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.74/0.99  thf('79', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i]:
% 0.74/0.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.74/0.99      inference('demod', [status(thm)], ['77', '78'])).
% 0.74/0.99  thf('80', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.74/0.99      inference('demod', [status(thm)], ['72', '79'])).
% 0.74/0.99  thf('81', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.74/0.99      inference('demod', [status(thm)], ['5', '66'])).
% 0.74/0.99  thf('82', plain,
% 0.74/0.99      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.74/0.99      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.74/0.99  thf('83', plain,
% 0.74/0.99      (![X62 : $i, X63 : $i]:
% 0.74/0.99         (((X63) = (k1_tarski @ X62))
% 0.74/0.99          | ((X63) = (k1_xboole_0))
% 0.74/0.99          | ~ (r1_tarski @ X63 @ (k1_tarski @ X62)))),
% 0.74/0.99      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.74/0.99  thf('84', plain,
% 0.74/0.99      (![X0 : $i, X1 : $i]:
% 0.74/0.99         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.74/0.99          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.74/0.99      inference('sup-', [status(thm)], ['82', '83'])).
% 0.74/0.99  thf('85', plain,
% 0.74/0.99      (![X0 : $i]:
% 0.74/0.99         (((k3_xboole_0 @ sk_B_1 @ X0) = (k1_tarski @ sk_A))
% 0.74/0.99          | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ X0) = (k1_xboole_0)))),
% 0.74/0.99      inference('sup+', [status(thm)], ['81', '84'])).
% 0.74/0.99  thf('86', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.74/0.99      inference('demod', [status(thm)], ['5', '66'])).
% 0.74/0.99  thf('87', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.74/0.99      inference('demod', [status(thm)], ['5', '66'])).
% 0.74/0.99  thf('88', plain,
% 0.74/0.99      (![X0 : $i]:
% 0.74/0.99         (((k3_xboole_0 @ sk_B_1 @ X0) = (sk_B_1))
% 0.74/0.99          | ((k3_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.74/0.99      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.74/0.99  thf('89', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.74/0.99      inference('demod', [status(thm)], ['72', '79'])).
% 0.74/0.99  thf('90', plain,
% 0.74/0.99      ((((k1_xboole_0) = (sk_C_2))
% 0.74/0.99        | ((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1)))),
% 0.74/0.99      inference('sup+', [status(thm)], ['88', '89'])).
% 0.74/0.99  thf('91', plain,
% 0.74/0.99      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.74/0.99      inference('split', [status(esa)], ['45'])).
% 0.74/0.99  thf('92', plain,
% 0.74/0.99      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('split', [status(esa)], ['45'])).
% 0.74/0.99  thf('93', plain,
% 0.74/0.99      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.74/0.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.99  thf('94', plain,
% 0.74/0.99      (![X59 : $i, X61 : $i]:
% 0.74/0.99         ((r1_tarski @ (k1_tarski @ X59) @ X61) | ~ (r2_hidden @ X59 @ X61))),
% 0.74/0.99      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.74/0.99  thf('95', plain,
% 0.74/0.99      (![X0 : $i]:
% 0.74/0.99         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.74/0.99      inference('sup-', [status(thm)], ['93', '94'])).
% 0.74/0.99  thf('96', plain,
% 0.74/0.99      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('simplify', [status(thm)], ['47'])).
% 0.74/0.99  thf('97', plain,
% 0.74/0.99      (![X63 : $i, X64 : $i]:
% 0.74/0.99         ((r1_tarski @ X63 @ (k1_tarski @ X64)) | ((X63) != (k1_xboole_0)))),
% 0.74/0.99      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.74/0.99  thf('98', plain,
% 0.74/0.99      (![X64 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X64))),
% 0.74/0.99      inference('simplify', [status(thm)], ['97'])).
% 0.74/0.99  thf('99', plain,
% 0.74/0.99      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ (k1_tarski @ X0)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup+', [status(thm)], ['96', '98'])).
% 0.74/0.99  thf('100', plain,
% 0.74/0.99      (![X11 : $i, X13 : $i]:
% 0.74/0.99         (((X11) = (X13))
% 0.74/0.99          | ~ (r1_tarski @ X13 @ X11)
% 0.74/0.99          | ~ (r1_tarski @ X11 @ X13))),
% 0.74/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.99  thf('101', plain,
% 0.74/0.99      ((![X0 : $i]:
% 0.74/0.99          (~ (r1_tarski @ (k1_tarski @ X0) @ sk_B_1)
% 0.74/0.99           | ((k1_tarski @ X0) = (sk_B_1))))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup-', [status(thm)], ['99', '100'])).
% 0.74/0.99  thf('102', plain,
% 0.74/0.99      ((((v1_xboole_0 @ sk_B_1) | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup-', [status(thm)], ['95', '101'])).
% 0.74/0.99  thf('103', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.74/0.99      inference('simplify_reflect-', [status(thm)], ['36', '53'])).
% 0.74/0.99  thf('104', plain,
% 0.74/0.99      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('clc', [status(thm)], ['102', '103'])).
% 0.74/0.99  thf('105', plain,
% 0.74/0.99      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('clc', [status(thm)], ['102', '103'])).
% 0.74/0.99  thf(t69_enumset1, axiom,
% 0.74/0.99    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.74/0.99  thf('106', plain,
% 0.74/0.99      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.74/0.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.74/0.99  thf(l51_zfmisc_1, axiom,
% 0.74/0.99    (![A:$i,B:$i]:
% 0.74/0.99     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.74/0.99  thf('107', plain,
% 0.74/0.99      (![X65 : $i, X66 : $i]:
% 0.74/0.99         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 0.74/0.99      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.74/0.99  thf('108', plain,
% 0.74/0.99      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.74/0.99      inference('sup+', [status(thm)], ['106', '107'])).
% 0.74/0.99  thf('109', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ X9) = (X9))),
% 0.74/0.99      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.74/0.99  thf('110', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.74/0.99      inference('demod', [status(thm)], ['108', '109'])).
% 0.74/0.99  thf('111', plain,
% 0.74/0.99      ((((k3_tarski @ sk_B_1) = (sk_B @ sk_B_1)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup+', [status(thm)], ['105', '110'])).
% 0.74/0.99  thf('112', plain,
% 0.74/0.99      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('demod', [status(thm)], ['104', '111'])).
% 0.74/0.99  thf('113', plain,
% 0.74/0.99      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.74/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.99  thf('114', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.74/0.99      inference('simplify', [status(thm)], ['113'])).
% 0.74/0.99  thf('115', plain,
% 0.74/0.99      (![X59 : $i, X60 : $i]:
% 0.74/0.99         ((r2_hidden @ X59 @ X60) | ~ (r1_tarski @ (k1_tarski @ X59) @ X60))),
% 0.74/0.99      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.74/0.99  thf('116', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.74/0.99      inference('sup-', [status(thm)], ['114', '115'])).
% 0.74/0.99  thf('117', plain,
% 0.74/0.99      (((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_B_1))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup+', [status(thm)], ['112', '116'])).
% 0.74/0.99  thf('118', plain,
% 0.74/0.99      (![X0 : $i]:
% 0.74/0.99         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.74/0.99      inference('sup-', [status(thm)], ['59', '60'])).
% 0.74/0.99  thf('119', plain,
% 0.74/0.99      (((r2_hidden @ (k3_tarski @ sk_B_1) @ (k1_tarski @ sk_A)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup-', [status(thm)], ['117', '118'])).
% 0.74/0.99  thf('120', plain,
% 0.74/0.99      (![X26 : $i, X29 : $i]:
% 0.74/0.99         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 0.74/0.99      inference('simplify', [status(thm)], ['63'])).
% 0.74/0.99  thf('121', plain,
% 0.74/0.99      ((((k3_tarski @ sk_B_1) = (sk_A)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('sup-', [status(thm)], ['119', '120'])).
% 0.74/0.99  thf('122', plain,
% 0.74/0.99      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1)))
% 0.74/0.99         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('demod', [status(thm)], ['104', '111'])).
% 0.74/0.99  thf('123', plain,
% 0.74/0.99      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.74/0.99      inference('demod', [status(thm)], ['92', '121', '122'])).
% 0.74/0.99  thf('124', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.74/0.99      inference('simplify', [status(thm)], ['123'])).
% 0.74/0.99  thf('125', plain,
% 0.74/0.99      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.74/0.99      inference('split', [status(esa)], ['45'])).
% 0.74/0.99  thf('126', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.74/0.99      inference('sat_resolution*', [status(thm)], ['124', '125'])).
% 0.74/0.99  thf('127', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.74/0.99      inference('simpl_trail', [status(thm)], ['91', '126'])).
% 0.74/0.99  thf('128', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1))),
% 0.74/0.99      inference('simplify_reflect-', [status(thm)], ['90', '127'])).
% 0.74/0.99  thf('129', plain, (((sk_C_2) = (sk_B_1))),
% 0.74/0.99      inference('sup+', [status(thm)], ['80', '128'])).
% 0.74/0.99  thf('130', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.74/0.99      inference('simpl_trail', [status(thm)], ['38', '52'])).
% 0.74/0.99  thf('131', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.74/0.99      inference('demod', [status(thm)], ['5', '66'])).
% 0.74/0.99  thf('132', plain, (((sk_C_2) != (sk_B_1))),
% 0.74/0.99      inference('demod', [status(thm)], ['130', '131'])).
% 0.74/0.99  thf('133', plain, ($false),
% 0.74/0.99      inference('simplify_reflect-', [status(thm)], ['129', '132'])).
% 0.74/0.99  
% 0.74/0.99  % SZS output end Refutation
% 0.74/0.99  
% 0.74/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
