%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hOPTF4cxW3

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:31 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  190 (2059 expanded)
%              Number of leaves         :   31 ( 599 expanded)
%              Depth                    :   35
%              Number of atoms          : 1268 (19185 expanded)
%              Number of equality atoms :  161 (2823 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('24',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_C_2 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('44',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('47',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ X0 )
         != k1_xboole_0 )
        | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('59',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['43','45','63'])).

thf('65',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','64'])).

thf('66',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['40','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('68',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','68'])).

thf('70',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','69'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('72',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('73',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('76',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('81',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('82',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','83'])).

thf('85',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['74','84'])).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','69'])).

thf('89',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('90',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('91',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['90'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('92',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('93',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( r2_hidden @ X63 @ X64 )
      | ~ ( r1_tarski @ ( k2_tarski @ X63 @ X65 ) @ X64 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X9 ) )
      | ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('99',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','68'])).

thf('103',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('104',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['101','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ sk_B_1 @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['97','109'])).

thf('111',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('112',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('113',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('115',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['102','107'])).

thf('117',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ sk_B_1 @ ( k5_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['110','117'])).

thf('119',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['89','118'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('120',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('121',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['101','108'])).

thf('125',plain,
    ( ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('127',plain,
    ( ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_B_1 = sk_C_2 )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['88','127'])).

thf('129',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','64'])).

thf('130',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','68'])).

thf('131',plain,(
    sk_C_2 != sk_B_1 ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['128','131'])).

thf('133',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['87','132'])).

thf('134',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('135',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('141',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('142',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('146',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['140','146'])).

thf('148',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['137','138','139','147'])).

thf('149',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['60'])).

thf('150',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['5','68'])).

thf('151',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['60'])).

thf('152',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['60'])).

thf('155',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['153','154'])).

thf('156',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['149','155'])).

thf('157',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['148','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hOPTF4cxW3
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.61/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.84  % Solved by: fo/fo7.sh
% 0.61/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.84  % done 1037 iterations in 0.377s
% 0.61/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.84  % SZS output start Refutation
% 0.61/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.61/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.84  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.61/0.84  thf(t43_zfmisc_1, conjecture,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.61/0.84          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.61/0.84          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.61/0.84          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.61/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.84    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.84        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.61/0.84             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.61/0.84             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.61/0.84             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.61/0.84    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.61/0.84  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(t7_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.84  thf('2', plain,
% 0.61/0.84      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.61/0.84      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.61/0.84  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.61/0.84      inference('sup+', [status(thm)], ['1', '2'])).
% 0.61/0.84  thf(d10_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.84  thf('4', plain,
% 0.61/0.84      (![X11 : $i, X13 : $i]:
% 0.61/0.84         (((X11) = (X13))
% 0.61/0.84          | ~ (r1_tarski @ X13 @ X11)
% 0.61/0.84          | ~ (r1_tarski @ X11 @ X13))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('5', plain,
% 0.61/0.84      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.61/0.84        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['3', '4'])).
% 0.61/0.84  thf(idempotence_k3_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.61/0.84  thf('6', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.61/0.84      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.61/0.84  thf(t100_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.84  thf('7', plain,
% 0.61/0.84      (![X14 : $i, X15 : $i]:
% 0.61/0.84         ((k4_xboole_0 @ X14 @ X15)
% 0.61/0.84           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.84  thf('8', plain,
% 0.61/0.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['6', '7'])).
% 0.61/0.84  thf(t92_xboole_1, axiom,
% 0.61/0.84    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.61/0.84  thf('9', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.61/0.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.84  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['8', '9'])).
% 0.61/0.84  thf(d3_tarski, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.84  thf('11', plain,
% 0.61/0.84      (![X1 : $i, X3 : $i]:
% 0.61/0.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.84  thf('12', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.61/0.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.84  thf(t1_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.61/0.84       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.61/0.84  thf('13', plain,
% 0.61/0.84      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X6 @ X7)
% 0.61/0.84          | ~ (r2_hidden @ X6 @ X8)
% 0.61/0.84          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.61/0.84  thf('14', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.61/0.84          | ~ (r2_hidden @ X1 @ X0)
% 0.61/0.84          | ~ (r2_hidden @ X1 @ X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.84  thf('15', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.61/0.84      inference('simplify', [status(thm)], ['14'])).
% 0.61/0.84  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.61/0.84      inference('condensation', [status(thm)], ['15'])).
% 0.61/0.84  thf('17', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.61/0.84      inference('sup-', [status(thm)], ['11', '16'])).
% 0.61/0.84  thf('18', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.61/0.84      inference('sup+', [status(thm)], ['10', '17'])).
% 0.61/0.84  thf('19', plain,
% 0.61/0.84      (![X1 : $i, X3 : $i]:
% 0.61/0.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.84  thf('20', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.61/0.84      inference('sup+', [status(thm)], ['1', '2'])).
% 0.61/0.84  thf('21', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.61/0.84          | (r2_hidden @ X0 @ X2)
% 0.61/0.84          | ~ (r1_tarski @ X1 @ X2))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.84  thf('22', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.84  thf('23', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((r1_tarski @ sk_B_1 @ X0)
% 0.61/0.84          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['19', '22'])).
% 0.61/0.84  thf(d1_tarski, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.61/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.61/0.84  thf('24', plain,
% 0.61/0.84      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X31 @ X30)
% 0.61/0.84          | ((X31) = (X28))
% 0.61/0.84          | ((X30) != (k1_tarski @ X28)))),
% 0.61/0.84      inference('cnf', [status(esa)], [d1_tarski])).
% 0.61/0.84  thf('25', plain,
% 0.61/0.84      (![X28 : $i, X31 : $i]:
% 0.61/0.84         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.61/0.84      inference('simplify', [status(thm)], ['24'])).
% 0.61/0.84  thf('26', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['23', '25'])).
% 0.61/0.84  thf('27', plain,
% 0.61/0.84      (![X1 : $i, X3 : $i]:
% 0.61/0.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.84  thf('28', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((r2_hidden @ sk_A @ sk_B_1)
% 0.61/0.84          | (r1_tarski @ sk_B_1 @ X0)
% 0.61/0.84          | (r1_tarski @ sk_B_1 @ X0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['26', '27'])).
% 0.61/0.84  thf('29', plain,
% 0.61/0.84      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.61/0.84      inference('simplify', [status(thm)], ['28'])).
% 0.61/0.84  thf('30', plain,
% 0.61/0.84      (![X11 : $i, X13 : $i]:
% 0.61/0.84         (((X11) = (X13))
% 0.61/0.84          | ~ (r1_tarski @ X13 @ X11)
% 0.61/0.84          | ~ (r1_tarski @ X11 @ X13))),
% 0.61/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.84  thf('31', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         ((r2_hidden @ sk_A @ sk_B_1)
% 0.61/0.84          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.61/0.84          | ((X0) = (sk_B_1)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.61/0.84  thf('32', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (((k4_xboole_0 @ X0 @ X0) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['18', '31'])).
% 0.61/0.84  thf('33', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('34', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (((k1_tarski @ sk_A)
% 0.61/0.84            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_C_2))
% 0.61/0.84          | (r2_hidden @ sk_A @ sk_B_1))),
% 0.61/0.84      inference('sup+', [status(thm)], ['32', '33'])).
% 0.61/0.84  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['8', '9'])).
% 0.61/0.84  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.61/0.84      inference('sup-', [status(thm)], ['11', '16'])).
% 0.61/0.84  thf(t12_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.61/0.84  thf('37', plain,
% 0.61/0.84      (![X16 : $i, X17 : $i]:
% 0.61/0.84         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.61/0.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.61/0.84  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['36', '37'])).
% 0.61/0.84  thf('39', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.61/0.84      inference('sup+', [status(thm)], ['35', '38'])).
% 0.61/0.84  thf('40', plain,
% 0.61/0.84      ((((k1_tarski @ sk_A) = (sk_C_2)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.61/0.84      inference('demod', [status(thm)], ['34', '39'])).
% 0.61/0.84  thf('41', plain,
% 0.61/0.84      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('42', plain,
% 0.61/0.84      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.61/0.84         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.61/0.84      inference('split', [status(esa)], ['41'])).
% 0.61/0.84  thf('43', plain,
% 0.61/0.84      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.61/0.84      inference('split', [status(esa)], ['41'])).
% 0.61/0.84  thf('44', plain,
% 0.61/0.84      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('45', plain,
% 0.61/0.84      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.61/0.84       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.61/0.84      inference('split', [status(esa)], ['44'])).
% 0.61/0.84  thf('46', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (((k4_xboole_0 @ X0 @ X0) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['18', '31'])).
% 0.61/0.84  thf('47', plain,
% 0.61/0.84      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.61/0.84      inference('split', [status(esa)], ['41'])).
% 0.61/0.84  thf('48', plain,
% 0.61/0.84      ((![X0 : $i]:
% 0.61/0.84          (((k4_xboole_0 @ X0 @ X0) != (k1_xboole_0))
% 0.61/0.84           | (r2_hidden @ sk_A @ sk_B_1)))
% 0.61/0.84         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['46', '47'])).
% 0.61/0.84  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['8', '9'])).
% 0.61/0.84  thf('50', plain,
% 0.61/0.84      (((r2_hidden @ sk_A @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.61/0.84      inference('simplify_reflect+', [status(thm)], ['48', '49'])).
% 0.61/0.84  thf('51', plain,
% 0.61/0.84      (![X1 : $i, X3 : $i]:
% 0.61/0.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.84  thf('52', plain,
% 0.61/0.84      (![X28 : $i, X31 : $i]:
% 0.61/0.84         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.61/0.84      inference('simplify', [status(thm)], ['24'])).
% 0.61/0.84  thf('53', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.61/0.84          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['51', '52'])).
% 0.61/0.84  thf('54', plain,
% 0.61/0.84      (![X1 : $i, X3 : $i]:
% 0.61/0.84         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.61/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.84  thf('55', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.61/0.84          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.61/0.84          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['53', '54'])).
% 0.61/0.84  thf('56', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.61/0.84      inference('simplify', [status(thm)], ['55'])).
% 0.61/0.84  thf('57', plain,
% 0.61/0.84      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.61/0.84         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['50', '56'])).
% 0.61/0.84  thf('58', plain,
% 0.61/0.84      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.61/0.84        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['3', '4'])).
% 0.61/0.84  thf('59', plain,
% 0.61/0.84      ((((k1_tarski @ sk_A) = (sk_B_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['57', '58'])).
% 0.61/0.84  thf('60', plain,
% 0.61/0.84      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('61', plain,
% 0.61/0.84      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.61/0.84         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.61/0.84      inference('split', [status(esa)], ['60'])).
% 0.61/0.84  thf('62', plain,
% 0.61/0.84      ((((sk_B_1) != (sk_B_1)))
% 0.61/0.84         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.61/0.84             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['59', '61'])).
% 0.61/0.84  thf('63', plain,
% 0.61/0.84      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.61/0.84      inference('simplify', [status(thm)], ['62'])).
% 0.61/0.84  thf('64', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.61/0.84      inference('sat_resolution*', [status(thm)], ['43', '45', '63'])).
% 0.61/0.84  thf('65', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.61/0.84      inference('simpl_trail', [status(thm)], ['42', '64'])).
% 0.61/0.84  thf('66', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.61/0.84      inference('simplify_reflect-', [status(thm)], ['40', '65'])).
% 0.61/0.84  thf('67', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.61/0.84      inference('simplify', [status(thm)], ['55'])).
% 0.61/0.84  thf('68', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.61/0.84      inference('sup-', [status(thm)], ['66', '67'])).
% 0.61/0.84  thf('69', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.61/0.84      inference('demod', [status(thm)], ['5', '68'])).
% 0.61/0.84  thf('70', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.61/0.84      inference('demod', [status(thm)], ['0', '69'])).
% 0.61/0.84  thf(t95_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( k3_xboole_0 @ A @ B ) =
% 0.61/0.84       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.61/0.84  thf('71', plain,
% 0.61/0.84      (![X26 : $i, X27 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ X26 @ X27)
% 0.61/0.84           = (k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ 
% 0.61/0.84              (k2_xboole_0 @ X26 @ X27)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.61/0.84  thf(t91_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.84       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.61/0.84  thf('72', plain,
% 0.61/0.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.61/0.84         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.61/0.84           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.84  thf('73', plain,
% 0.61/0.84      (![X26 : $i, X27 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ X26 @ X27)
% 0.61/0.84           = (k5_xboole_0 @ X26 @ 
% 0.61/0.84              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 0.61/0.84      inference('demod', [status(thm)], ['71', '72'])).
% 0.61/0.84  thf('74', plain,
% 0.61/0.84      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.61/0.84         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ sk_B_1)))),
% 0.61/0.84      inference('sup+', [status(thm)], ['70', '73'])).
% 0.61/0.84  thf('75', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.61/0.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.84  thf('76', plain,
% 0.61/0.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.61/0.84         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.61/0.84           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.61/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.85  thf('77', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.61/0.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.85      inference('sup+', [status(thm)], ['75', '76'])).
% 0.61/0.85  thf('78', plain,
% 0.61/0.85      (![X26 : $i, X27 : $i]:
% 0.61/0.85         ((k3_xboole_0 @ X26 @ X27)
% 0.61/0.85           = (k5_xboole_0 @ X26 @ 
% 0.61/0.85              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 0.61/0.85      inference('demod', [status(thm)], ['71', '72'])).
% 0.61/0.85  thf('79', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.61/0.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.85      inference('sup+', [status(thm)], ['75', '76'])).
% 0.61/0.85  thf('80', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.61/0.85           = (k3_xboole_0 @ X0 @ X0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['78', '79'])).
% 0.61/0.85  thf(idempotence_k2_xboole_0, axiom,
% 0.61/0.85    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.61/0.85  thf('81', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.61/0.85      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.61/0.85  thf('82', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.61/0.85      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.61/0.85  thf('83', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.85      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.61/0.85  thf('84', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.85      inference('demod', [status(thm)], ['77', '83'])).
% 0.61/0.85  thf('85', plain,
% 0.61/0.85      (((k5_xboole_0 @ sk_C_2 @ sk_B_1)
% 0.61/0.85         = (k5_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.61/0.85      inference('sup+', [status(thm)], ['74', '84'])).
% 0.61/0.85  thf('86', plain,
% 0.61/0.85      (![X14 : $i, X15 : $i]:
% 0.61/0.85         ((k4_xboole_0 @ X14 @ X15)
% 0.61/0.85           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.61/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.85  thf('87', plain,
% 0.61/0.85      (((k5_xboole_0 @ sk_C_2 @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.61/0.85      inference('demod', [status(thm)], ['85', '86'])).
% 0.61/0.85  thf('88', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.61/0.85      inference('demod', [status(thm)], ['0', '69'])).
% 0.61/0.85  thf('89', plain,
% 0.61/0.85      (((k5_xboole_0 @ sk_C_2 @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.61/0.85      inference('demod', [status(thm)], ['85', '86'])).
% 0.61/0.85  thf('90', plain,
% 0.61/0.85      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.61/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.85  thf('91', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.61/0.85      inference('simplify', [status(thm)], ['90'])).
% 0.61/0.85  thf(t69_enumset1, axiom,
% 0.61/0.85    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.61/0.85  thf('92', plain,
% 0.61/0.85      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.61/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.85  thf(t38_zfmisc_1, axiom,
% 0.61/0.85    (![A:$i,B:$i,C:$i]:
% 0.61/0.85     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.61/0.85       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.61/0.85  thf('93', plain,
% 0.61/0.85      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.61/0.85         ((r2_hidden @ X63 @ X64)
% 0.61/0.85          | ~ (r1_tarski @ (k2_tarski @ X63 @ X65) @ X64))),
% 0.61/0.85      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.61/0.85  thf('94', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['92', '93'])).
% 0.61/0.85  thf('95', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.61/0.85      inference('sup-', [status(thm)], ['91', '94'])).
% 0.61/0.85  thf('96', plain,
% 0.61/0.85      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.61/0.85         ((r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X9))
% 0.61/0.85          | (r2_hidden @ X6 @ X7)
% 0.61/0.85          | ~ (r2_hidden @ X6 @ X9))),
% 0.61/0.85      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.61/0.85  thf('97', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((r2_hidden @ X0 @ X1)
% 0.61/0.85          | (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['95', '96'])).
% 0.61/0.85  thf('98', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['23', '25'])).
% 0.61/0.85  thf('99', plain,
% 0.61/0.85      (![X1 : $i, X3 : $i]:
% 0.61/0.85         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.61/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.85  thf('100', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (~ (r2_hidden @ sk_A @ X0)
% 0.61/0.85          | (r1_tarski @ sk_B_1 @ X0)
% 0.61/0.85          | (r1_tarski @ sk_B_1 @ X0))),
% 0.61/0.85      inference('sup-', [status(thm)], ['98', '99'])).
% 0.61/0.85  thf('101', plain,
% 0.61/0.85      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.61/0.85      inference('simplify', [status(thm)], ['100'])).
% 0.61/0.85  thf('102', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.61/0.85      inference('demod', [status(thm)], ['5', '68'])).
% 0.61/0.85  thf('103', plain,
% 0.61/0.85      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.61/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.85  thf(l51_zfmisc_1, axiom,
% 0.61/0.85    (![A:$i,B:$i]:
% 0.61/0.85     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.85  thf('104', plain,
% 0.61/0.85      (![X61 : $i, X62 : $i]:
% 0.61/0.85         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 0.61/0.85      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.61/0.85  thf('105', plain,
% 0.61/0.85      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['103', '104'])).
% 0.61/0.85  thf('106', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.61/0.85      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.61/0.85  thf('107', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.61/0.85      inference('demod', [status(thm)], ['105', '106'])).
% 0.61/0.85  thf('108', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.61/0.85      inference('sup+', [status(thm)], ['102', '107'])).
% 0.61/0.85  thf('109', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 0.61/0.85      inference('demod', [status(thm)], ['101', '108'])).
% 0.61/0.85  thf('110', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((r2_hidden @ (k3_tarski @ sk_B_1) @ X0)
% 0.61/0.85          | (r1_tarski @ sk_B_1 @ 
% 0.61/0.85             (k5_xboole_0 @ X0 @ (k1_tarski @ (k3_tarski @ sk_B_1)))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['97', '109'])).
% 0.61/0.85  thf('111', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.61/0.85      inference('sup-', [status(thm)], ['66', '67'])).
% 0.61/0.85  thf('112', plain,
% 0.61/0.85      (![X11 : $i, X13 : $i]:
% 0.61/0.85         (((X11) = (X13))
% 0.61/0.85          | ~ (r1_tarski @ X13 @ X11)
% 0.61/0.85          | ~ (r1_tarski @ X11 @ X13))),
% 0.61/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.85  thf('113', plain,
% 0.61/0.85      ((~ (r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.61/0.85        | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['111', '112'])).
% 0.61/0.85  thf('114', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.61/0.85      inference('sup+', [status(thm)], ['1', '2'])).
% 0.61/0.85  thf('115', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.61/0.85      inference('demod', [status(thm)], ['113', '114'])).
% 0.61/0.85  thf('116', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.61/0.85      inference('sup+', [status(thm)], ['102', '107'])).
% 0.61/0.85  thf('117', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.61/0.85      inference('demod', [status(thm)], ['115', '116'])).
% 0.61/0.85  thf('118', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((r2_hidden @ (k3_tarski @ sk_B_1) @ X0)
% 0.61/0.85          | (r1_tarski @ sk_B_1 @ (k5_xboole_0 @ X0 @ sk_B_1)))),
% 0.61/0.85      inference('demod', [status(thm)], ['110', '117'])).
% 0.61/0.85  thf('119', plain,
% 0.61/0.85      (((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.61/0.85        | (r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2))),
% 0.61/0.85      inference('sup+', [status(thm)], ['89', '118'])).
% 0.61/0.85  thf(t36_xboole_1, axiom,
% 0.61/0.85    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.85  thf('120', plain,
% 0.61/0.85      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.61/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.85  thf('121', plain,
% 0.61/0.85      (![X11 : $i, X13 : $i]:
% 0.61/0.85         (((X11) = (X13))
% 0.61/0.85          | ~ (r1_tarski @ X13 @ X11)
% 0.61/0.85          | ~ (r1_tarski @ X11 @ X13))),
% 0.61/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.85  thf('122', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.61/0.85          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['120', '121'])).
% 0.61/0.85  thf('123', plain,
% 0.61/0.85      (((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2)
% 0.61/0.85        | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['119', '122'])).
% 0.61/0.85  thf('124', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 0.61/0.85      inference('demod', [status(thm)], ['101', '108'])).
% 0.61/0.85  thf('125', plain,
% 0.61/0.85      ((((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.61/0.85        | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.61/0.85      inference('sup-', [status(thm)], ['123', '124'])).
% 0.61/0.85  thf('126', plain,
% 0.61/0.85      (![X16 : $i, X17 : $i]:
% 0.61/0.85         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.61/0.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.61/0.85  thf('127', plain,
% 0.61/0.85      ((((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.61/0.85        | ((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['125', '126'])).
% 0.61/0.85  thf('128', plain,
% 0.61/0.85      ((((sk_B_1) = (sk_C_2)) | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.61/0.85      inference('sup+', [status(thm)], ['88', '127'])).
% 0.61/0.85  thf('129', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.61/0.85      inference('simpl_trail', [status(thm)], ['42', '64'])).
% 0.61/0.85  thf('130', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.61/0.85      inference('demod', [status(thm)], ['5', '68'])).
% 0.61/0.85  thf('131', plain, (((sk_C_2) != (sk_B_1))),
% 0.61/0.85      inference('demod', [status(thm)], ['129', '130'])).
% 0.61/0.85  thf('132', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.61/0.85      inference('simplify_reflect-', [status(thm)], ['128', '131'])).
% 0.61/0.85  thf('133', plain, (((k5_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_B_1))),
% 0.61/0.85      inference('demod', [status(thm)], ['87', '132'])).
% 0.61/0.85  thf('134', plain,
% 0.61/0.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.61/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.61/0.85           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.61/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.85  thf('135', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.61/0.85      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.85  thf('136', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.61/0.85           = (k1_xboole_0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['134', '135'])).
% 0.61/0.85  thf('137', plain,
% 0.61/0.85      (((k5_xboole_0 @ sk_C_2 @ (k5_xboole_0 @ sk_B_1 @ sk_B_1))
% 0.61/0.85         = (k1_xboole_0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['133', '136'])).
% 0.61/0.85  thf('138', plain,
% 0.61/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['6', '7'])).
% 0.61/0.85  thf('139', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['8', '9'])).
% 0.61/0.85  thf('140', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['8', '9'])).
% 0.61/0.85  thf('141', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.61/0.85      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.61/0.85  thf('142', plain,
% 0.61/0.85      (![X26 : $i, X27 : $i]:
% 0.61/0.85         ((k3_xboole_0 @ X26 @ X27)
% 0.61/0.85           = (k5_xboole_0 @ X26 @ 
% 0.61/0.85              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 0.61/0.85      inference('demod', [status(thm)], ['71', '72'])).
% 0.61/0.85  thf('143', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((k3_xboole_0 @ X0 @ X0)
% 0.61/0.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.61/0.85      inference('sup+', [status(thm)], ['141', '142'])).
% 0.61/0.85  thf('144', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.61/0.85      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.61/0.85  thf('145', plain,
% 0.61/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['6', '7'])).
% 0.61/0.85  thf('146', plain,
% 0.61/0.85      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.61/0.85      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.61/0.85  thf('147', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['140', '146'])).
% 0.61/0.85  thf('148', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.61/0.85      inference('demod', [status(thm)], ['137', '138', '139', '147'])).
% 0.61/0.85  thf('149', plain,
% 0.61/0.85      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.61/0.85      inference('split', [status(esa)], ['60'])).
% 0.61/0.85  thf('150', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.61/0.85      inference('demod', [status(thm)], ['5', '68'])).
% 0.61/0.85  thf('151', plain,
% 0.61/0.85      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.61/0.85         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.61/0.85      inference('split', [status(esa)], ['60'])).
% 0.61/0.85  thf('152', plain,
% 0.61/0.85      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['150', '151'])).
% 0.61/0.85  thf('153', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.61/0.85      inference('simplify', [status(thm)], ['152'])).
% 0.61/0.85  thf('154', plain,
% 0.61/0.85      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.61/0.85      inference('split', [status(esa)], ['60'])).
% 0.61/0.85  thf('155', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.61/0.85      inference('sat_resolution*', [status(thm)], ['153', '154'])).
% 0.61/0.85  thf('156', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.61/0.85      inference('simpl_trail', [status(thm)], ['149', '155'])).
% 0.61/0.85  thf('157', plain, ($false),
% 0.61/0.85      inference('simplify_reflect-', [status(thm)], ['148', '156'])).
% 0.61/0.85  
% 0.61/0.85  % SZS output end Refutation
% 0.61/0.85  
% 0.61/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
