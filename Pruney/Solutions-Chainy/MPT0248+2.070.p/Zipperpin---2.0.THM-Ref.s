%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iynumB5iQl

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:28 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  194 (1356 expanded)
%              Number of leaves         :   35 ( 390 expanded)
%              Depth                    :   35
%              Number of atoms          : 1340 (13813 expanded)
%              Number of equality atoms :  213 (2522 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X61: $i,X63: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X61 ) @ X63 )
      | ~ ( r2_hidden @ X61 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B_1 )
        = sk_A )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B_1 )
        = sk_A )
      | ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( ( k3_tarski @ sk_B_1 )
      = sk_A ) ),
    inference('sup+',[status(thm)],['1','28'])).

thf('30',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('33',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('37',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('39',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X61: $i,X63: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X61 ) @ X63 )
      | ~ ( r2_hidden @ X61 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('44',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('52',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['32','34','53'])).

thf('55',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['31','54'])).

thf('56',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['29','55'])).

thf('57',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','56'])).

thf('58',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('61',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('63',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','56'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('67',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('68',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('69',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('70',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('73',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','75'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('80',plain,
    ( ( ( k5_xboole_0 @ sk_C_2 @ sk_B_1 )
      = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('82',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('84',plain,
    ( ( sk_C_2
      = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_C_2
      = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('90',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','94'])).

thf('96',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('97',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('99',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('100',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('101',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('107',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ X0 ) )
        | ( ( k1_tarski @ sk_A )
          = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('110',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('111',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('112',plain,(
    ! [X66: $i,X67: $i] :
      ( ( X67 != X66 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X67 ) @ ( k1_tarski @ X66 ) )
       != ( k1_tarski @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('113',plain,(
    ! [X66: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X66 ) @ ( k1_tarski @ X66 ) )
     != ( k1_tarski @ X66 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('115',plain,(
    ! [X66: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X66 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( sk_B_1
       != ( k2_tarski @ X0 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( sk_B_1
       != ( k1_tarski @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','117'])).

thf('119',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','118'])).

thf('120',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','119'])).

thf('121',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','120'])).

thf('122',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['97','123'])).

thf('125',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['31','54'])).

thf('126',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('128',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['126','127'])).

thf('129',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['96','128'])).

thf('130',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['95','129'])).

thf('131',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('132',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_2 )
      = ( k3_tarski @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,
    ( ( ( sk_B @ sk_C_2 )
      = ( k3_tarski @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('137',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['96','128'])).

thf('139',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('141',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['29','55'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['139','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('148',plain,(
    ! [X66: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X66 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != sk_B_1 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(clc,[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('152',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['57','152'])).

thf('154',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['31','54'])).

thf('155',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['29','55'])).

thf('156',plain,(
    sk_C_2
 != ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['153','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iynumB5iQl
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.92/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.10  % Solved by: fo/fo7.sh
% 0.92/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.10  % done 1698 iterations in 0.648s
% 0.92/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.10  % SZS output start Refutation
% 0.92/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.92/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.10  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.92/1.10  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.92/1.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.92/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.92/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(sk_B_type, type, sk_B: $i > $i).
% 0.92/1.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.92/1.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.92/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.10  thf(t43_zfmisc_1, conjecture,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.92/1.10          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.92/1.10          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.92/1.10          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.92/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.10    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.10        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.92/1.10             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.92/1.10             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.92/1.10             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.92/1.10    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.92/1.10  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(d3_tarski, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( r1_tarski @ A @ B ) <=>
% 0.92/1.10       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.92/1.10  thf('2', plain,
% 0.92/1.10      (![X3 : $i, X5 : $i]:
% 0.92/1.10         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.92/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.10  thf('3', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(t7_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.92/1.10  thf('4', plain,
% 0.92/1.10      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.92/1.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.92/1.10  thf('5', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.92/1.10      inference('sup+', [status(thm)], ['3', '4'])).
% 0.92/1.10  thf('6', plain,
% 0.92/1.10      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X2 @ X3)
% 0.92/1.10          | (r2_hidden @ X2 @ X4)
% 0.92/1.10          | ~ (r1_tarski @ X3 @ X4))),
% 0.92/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.10  thf('7', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.92/1.10      inference('sup-', [status(thm)], ['5', '6'])).
% 0.92/1.10  thf('8', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_tarski @ sk_B_1 @ X0)
% 0.92/1.10          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['2', '7'])).
% 0.92/1.10  thf(d1_tarski, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.92/1.10       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.92/1.10  thf('9', plain,
% 0.92/1.10      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X31 @ X30)
% 0.92/1.10          | ((X31) = (X28))
% 0.92/1.10          | ((X30) != (k1_tarski @ X28)))),
% 0.92/1.10      inference('cnf', [status(esa)], [d1_tarski])).
% 0.92/1.10  thf('10', plain,
% 0.92/1.10      (![X28 : $i, X31 : $i]:
% 0.92/1.10         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['9'])).
% 0.92/1.10  thf('11', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['8', '10'])).
% 0.92/1.10  thf('12', plain,
% 0.92/1.10      (![X3 : $i, X5 : $i]:
% 0.92/1.10         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.92/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.10  thf(l1_zfmisc_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.92/1.10  thf('13', plain,
% 0.92/1.10      (![X61 : $i, X63 : $i]:
% 0.92/1.10         ((r1_tarski @ (k1_tarski @ X61) @ X63) | ~ (r2_hidden @ X61 @ X63))),
% 0.92/1.10      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.92/1.10  thf('14', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((r1_tarski @ X0 @ X1)
% 0.92/1.10          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.92/1.10      inference('sup-', [status(thm)], ['12', '13'])).
% 0.92/1.10  thf('15', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.92/1.10          | (r1_tarski @ sk_B_1 @ X0)
% 0.92/1.10          | (r1_tarski @ sk_B_1 @ X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['11', '14'])).
% 0.92/1.10  thf('16', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_tarski @ sk_B_1 @ X0) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.92/1.10      inference('simplify', [status(thm)], ['15'])).
% 0.92/1.10  thf('17', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.92/1.10      inference('sup+', [status(thm)], ['3', '4'])).
% 0.92/1.10  thf(d10_xboole_0, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.92/1.10  thf('18', plain,
% 0.92/1.10      (![X9 : $i, X11 : $i]:
% 0.92/1.10         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.92/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.92/1.10  thf('19', plain,
% 0.92/1.10      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.92/1.10        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['17', '18'])).
% 0.92/1.10  thf('20', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_tarski @ sk_B_1 @ X0) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['16', '19'])).
% 0.92/1.10  thf(t69_enumset1, axiom,
% 0.92/1.10    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.92/1.10  thf('21', plain,
% 0.92/1.10      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.92/1.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.92/1.10  thf(l51_zfmisc_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.92/1.10  thf('22', plain,
% 0.92/1.10      (![X64 : $i, X65 : $i]:
% 0.92/1.10         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 0.92/1.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.92/1.10  thf('23', plain,
% 0.92/1.10      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['21', '22'])).
% 0.92/1.10  thf(idempotence_k2_xboole_0, axiom,
% 0.92/1.10    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.92/1.10  thf('24', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.92/1.10      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.92/1.10  thf('25', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['23', '24'])).
% 0.92/1.10  thf('26', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (((k3_tarski @ sk_B_1) = (sk_A)) | (r1_tarski @ sk_B_1 @ X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['20', '25'])).
% 0.92/1.10  thf(t12_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.92/1.10  thf('27', plain,
% 0.92/1.10      (![X14 : $i, X15 : $i]:
% 0.92/1.10         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.92/1.10      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.92/1.10  thf('28', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (((k3_tarski @ sk_B_1) = (sk_A))
% 0.92/1.10          | ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['26', '27'])).
% 0.92/1.10  thf('29', plain,
% 0.92/1.10      ((((k1_tarski @ sk_A) = (sk_C_2)) | ((k3_tarski @ sk_B_1) = (sk_A)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['1', '28'])).
% 0.92/1.10  thf('30', plain,
% 0.92/1.10      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('31', plain,
% 0.92/1.10      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.92/1.10         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('split', [status(esa)], ['30'])).
% 0.92/1.10  thf('32', plain,
% 0.92/1.10      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('split', [status(esa)], ['30'])).
% 0.92/1.10  thf('33', plain,
% 0.92/1.10      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('34', plain,
% 0.92/1.10      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.92/1.10       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.92/1.10      inference('split', [status(esa)], ['33'])).
% 0.92/1.10  thf(t7_xboole_0, axiom,
% 0.92/1.10    (![A:$i]:
% 0.92/1.10     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.92/1.10          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.92/1.10  thf('35', plain,
% 0.92/1.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.92/1.10      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.92/1.10  thf('36', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.92/1.10      inference('sup-', [status(thm)], ['5', '6'])).
% 0.92/1.10  thf('37', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0))
% 0.92/1.10        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['35', '36'])).
% 0.92/1.10  thf('38', plain,
% 0.92/1.10      (![X28 : $i, X31 : $i]:
% 0.92/1.10         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['9'])).
% 0.92/1.10  thf('39', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B @ sk_B_1) = (sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['37', '38'])).
% 0.92/1.10  thf('40', plain,
% 0.92/1.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.92/1.10      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.92/1.10  thf('41', plain,
% 0.92/1.10      (((r2_hidden @ sk_A @ sk_B_1)
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0))
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['39', '40'])).
% 0.92/1.10  thf('42', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.92/1.10      inference('simplify', [status(thm)], ['41'])).
% 0.92/1.10  thf('43', plain,
% 0.92/1.10      (![X61 : $i, X63 : $i]:
% 0.92/1.10         ((r1_tarski @ (k1_tarski @ X61) @ X63) | ~ (r2_hidden @ X61 @ X63))),
% 0.92/1.10      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.92/1.10  thf('44', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.92/1.10      inference('sup-', [status(thm)], ['42', '43'])).
% 0.92/1.10  thf('45', plain,
% 0.92/1.10      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.92/1.10        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['17', '18'])).
% 0.92/1.10  thf('46', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['44', '45'])).
% 0.92/1.10  thf('47', plain,
% 0.92/1.10      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('48', plain,
% 0.92/1.10      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('split', [status(esa)], ['47'])).
% 0.92/1.10  thf('49', plain,
% 0.92/1.10      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['46', '48'])).
% 0.92/1.10  thf('50', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('simplify', [status(thm)], ['49'])).
% 0.92/1.10  thf('51', plain,
% 0.92/1.10      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.92/1.10      inference('split', [status(esa)], ['30'])).
% 0.92/1.10  thf('52', plain,
% 0.92/1.10      ((((sk_B_1) != (sk_B_1)))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.92/1.10             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['50', '51'])).
% 0.92/1.10  thf('53', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['52'])).
% 0.92/1.10  thf('54', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.92/1.10      inference('sat_resolution*', [status(thm)], ['32', '34', '53'])).
% 0.92/1.10  thf('55', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.92/1.10      inference('simpl_trail', [status(thm)], ['31', '54'])).
% 0.92/1.10  thf('56', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['29', '55'])).
% 0.92/1.10  thf('57', plain,
% 0.92/1.10      (((k1_tarski @ (k3_tarski @ sk_B_1)) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.92/1.10      inference('demod', [status(thm)], ['0', '56'])).
% 0.92/1.10  thf('58', plain,
% 0.92/1.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.92/1.10      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.92/1.10  thf('59', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['44', '45'])).
% 0.92/1.10  thf('60', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['23', '24'])).
% 0.92/1.10  thf('61', plain,
% 0.92/1.10      ((((k3_tarski @ sk_B_1) = (sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['59', '60'])).
% 0.92/1.10  thf('62', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['44', '45'])).
% 0.92/1.10  thf('63', plain,
% 0.92/1.10      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0))
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['61', '62'])).
% 0.92/1.10  thf('64', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0))
% 0.92/1.10        | ((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['63'])).
% 0.92/1.10  thf('65', plain,
% 0.92/1.10      (((k1_tarski @ (k3_tarski @ sk_B_1)) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.92/1.10      inference('demod', [status(thm)], ['0', '56'])).
% 0.92/1.10  thf(t95_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( k3_xboole_0 @ A @ B ) =
% 0.92/1.10       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.92/1.10  thf('66', plain,
% 0.92/1.10      (![X26 : $i, X27 : $i]:
% 0.92/1.10         ((k3_xboole_0 @ X26 @ X27)
% 0.92/1.10           = (k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ 
% 0.92/1.10              (k2_xboole_0 @ X26 @ X27)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.92/1.10  thf(t91_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.92/1.10       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.92/1.10  thf('67', plain,
% 0.92/1.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.92/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.92/1.10           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.92/1.10  thf('68', plain,
% 0.92/1.10      (![X26 : $i, X27 : $i]:
% 0.92/1.10         ((k3_xboole_0 @ X26 @ X27)
% 0.92/1.10           = (k5_xboole_0 @ X26 @ 
% 0.92/1.10              (k5_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X27))))),
% 0.92/1.10      inference('demod', [status(thm)], ['66', '67'])).
% 0.92/1.10  thf(t92_xboole_1, axiom,
% 0.92/1.10    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.92/1.10  thf('69', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.92/1.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.92/1.10  thf('70', plain,
% 0.92/1.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.92/1.10         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.92/1.10           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.92/1.10  thf('71', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.92/1.10           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['69', '70'])).
% 0.92/1.10  thf(commutativity_k5_xboole_0, axiom,
% 0.92/1.10    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.92/1.10  thf('72', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.92/1.10  thf(t5_boole, axiom,
% 0.92/1.10    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.92/1.10  thf('73', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.92/1.10      inference('cnf', [status(esa)], [t5_boole])).
% 0.92/1.10  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['72', '73'])).
% 0.92/1.10  thf('75', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['71', '74'])).
% 0.92/1.10  thf('76', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.92/1.10           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['68', '75'])).
% 0.92/1.10  thf(t100_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.92/1.10  thf('77', plain,
% 0.92/1.10      (![X12 : $i, X13 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X12 @ X13)
% 0.92/1.10           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.92/1.10  thf('78', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.92/1.10           = (k4_xboole_0 @ X1 @ X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['76', '77'])).
% 0.92/1.10  thf('79', plain,
% 0.92/1.10      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ (k3_tarski @ sk_B_1)))
% 0.92/1.10         = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.92/1.10      inference('sup+', [status(thm)], ['65', '78'])).
% 0.92/1.10  thf('80', plain,
% 0.92/1.10      ((((k5_xboole_0 @ sk_C_2 @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['64', '79'])).
% 0.92/1.10  thf('81', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.92/1.10  thf('82', plain,
% 0.92/1.10      ((((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['80', '81'])).
% 0.92/1.10  thf('83', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['71', '74'])).
% 0.92/1.10  thf('84', plain,
% 0.92/1.10      ((((sk_C_2) = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['82', '83'])).
% 0.92/1.10  thf('85', plain,
% 0.92/1.10      (![X12 : $i, X13 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X12 @ X13)
% 0.92/1.10           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.92/1.10  thf('86', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['71', '74'])).
% 0.92/1.10  thf('87', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k3_xboole_0 @ X1 @ X0)
% 0.92/1.10           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['85', '86'])).
% 0.92/1.10  thf('88', plain,
% 0.92/1.10      ((((sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['84', '87'])).
% 0.92/1.10  thf('89', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.92/1.10      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.92/1.10  thf(t29_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.92/1.10  thf('90', plain,
% 0.92/1.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.92/1.10         (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ (k2_xboole_0 @ X16 @ X18))),
% 0.92/1.10      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.92/1.10  thf('91', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.92/1.10      inference('sup+', [status(thm)], ['89', '90'])).
% 0.92/1.10  thf('92', plain,
% 0.92/1.10      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X2 @ X3)
% 0.92/1.10          | (r2_hidden @ X2 @ X4)
% 0.92/1.10          | ~ (r1_tarski @ X3 @ X4))),
% 0.92/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.10  thf('93', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['91', '92'])).
% 0.92/1.10  thf('94', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X0 @ sk_C_2)
% 0.92/1.10          | ((sk_B_1) = (k1_xboole_0))
% 0.92/1.10          | (r2_hidden @ X0 @ sk_B_1))),
% 0.92/1.10      inference('sup-', [status(thm)], ['88', '93'])).
% 0.92/1.10  thf('95', plain,
% 0.92/1.10      ((((sk_C_2) = (k1_xboole_0))
% 0.92/1.10        | (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['58', '94'])).
% 0.92/1.10  thf('96', plain,
% 0.92/1.10      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.92/1.10      inference('split', [status(esa)], ['47'])).
% 0.92/1.10  thf('97', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('98', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_tarski @ sk_B_1 @ X0) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.92/1.10      inference('simplify', [status(thm)], ['15'])).
% 0.92/1.10  thf('99', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('simplify', [status(thm)], ['49'])).
% 0.92/1.10  thf(idempotence_k3_xboole_0, axiom,
% 0.92/1.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.92/1.10  thf('100', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.92/1.10      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.92/1.10  thf('101', plain,
% 0.92/1.10      (![X12 : $i, X13 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X12 @ X13)
% 0.92/1.10           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.92/1.10  thf('102', plain,
% 0.92/1.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['100', '101'])).
% 0.92/1.10  thf('103', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.92/1.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.92/1.10  thf('104', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['102', '103'])).
% 0.92/1.10  thf('105', plain,
% 0.92/1.10      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (sk_B_1)))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup+', [status(thm)], ['99', '104'])).
% 0.92/1.10  thf('106', plain,
% 0.92/1.10      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (sk_B_1)))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup+', [status(thm)], ['99', '104'])).
% 0.92/1.10  thf('107', plain,
% 0.92/1.10      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.92/1.10        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['17', '18'])).
% 0.92/1.10  thf('108', plain,
% 0.92/1.10      ((![X0 : $i]:
% 0.92/1.10          (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ X0))
% 0.92/1.10           | ((k1_tarski @ sk_A) = (sk_B_1))))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['106', '107'])).
% 0.92/1.10  thf('109', plain,
% 0.92/1.10      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.92/1.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.92/1.10  thf('110', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('simplify', [status(thm)], ['49'])).
% 0.92/1.10  thf('111', plain,
% 0.92/1.10      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.92/1.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.92/1.10  thf(t20_zfmisc_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.92/1.10         ( k1_tarski @ A ) ) <=>
% 0.92/1.10       ( ( A ) != ( B ) ) ))).
% 0.92/1.10  thf('112', plain,
% 0.92/1.10      (![X66 : $i, X67 : $i]:
% 0.92/1.10         (((X67) != (X66))
% 0.92/1.10          | ((k4_xboole_0 @ (k1_tarski @ X67) @ (k1_tarski @ X66))
% 0.92/1.10              != (k1_tarski @ X67)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.92/1.10  thf('113', plain,
% 0.92/1.10      (![X66 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ (k1_tarski @ X66) @ (k1_tarski @ X66))
% 0.92/1.10           != (k1_tarski @ X66))),
% 0.92/1.10      inference('simplify', [status(thm)], ['112'])).
% 0.92/1.10  thf('114', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['102', '103'])).
% 0.92/1.10  thf('115', plain, (![X66 : $i]: ((k1_xboole_0) != (k1_tarski @ X66))),
% 0.92/1.10      inference('demod', [status(thm)], ['113', '114'])).
% 0.92/1.10  thf('116', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 0.92/1.10      inference('sup-', [status(thm)], ['111', '115'])).
% 0.92/1.10  thf('117', plain,
% 0.92/1.10      ((![X0 : $i]: ((sk_B_1) != (k2_tarski @ X0 @ X0)))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['110', '116'])).
% 0.92/1.10  thf('118', plain,
% 0.92/1.10      ((![X0 : $i]: ((sk_B_1) != (k1_tarski @ X0)))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['109', '117'])).
% 0.92/1.10  thf('119', plain,
% 0.92/1.10      ((![X0 : $i]:
% 0.92/1.10          ~ (r1_tarski @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ X0)))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('clc', [status(thm)], ['108', '118'])).
% 0.92/1.10  thf('120', plain,
% 0.92/1.10      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['105', '119'])).
% 0.92/1.10  thf('121', plain,
% 0.92/1.10      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['98', '120'])).
% 0.92/1.10  thf('122', plain,
% 0.92/1.10      (![X14 : $i, X15 : $i]:
% 0.92/1.10         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.92/1.10      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.92/1.10  thf('123', plain,
% 0.92/1.10      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['121', '122'])).
% 0.92/1.10  thf('124', plain,
% 0.92/1.10      ((((k1_tarski @ sk_A) = (sk_C_2)))
% 0.92/1.10         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.92/1.10      inference('sup+', [status(thm)], ['97', '123'])).
% 0.92/1.10  thf('125', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.92/1.10      inference('simpl_trail', [status(thm)], ['31', '54'])).
% 0.92/1.10  thf('126', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 0.92/1.10  thf('127', plain,
% 0.92/1.10      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.92/1.10      inference('split', [status(esa)], ['47'])).
% 0.92/1.10  thf('128', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.92/1.10      inference('sat_resolution*', [status(thm)], ['126', '127'])).
% 0.92/1.10  thf('129', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.92/1.10      inference('simpl_trail', [status(thm)], ['96', '128'])).
% 0.92/1.10  thf('130', plain,
% 0.92/1.10      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['95', '129'])).
% 0.92/1.10  thf('131', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0))
% 0.92/1.10        | ((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['63'])).
% 0.92/1.10  thf('132', plain,
% 0.92/1.10      (![X28 : $i, X31 : $i]:
% 0.92/1.10         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['9'])).
% 0.92/1.10  thf('133', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.92/1.10          | ((sk_B_1) = (k1_xboole_0))
% 0.92/1.10          | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['131', '132'])).
% 0.92/1.10  thf('134', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0))
% 0.92/1.10        | ((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['130', '133'])).
% 0.92/1.10  thf('135', plain,
% 0.92/1.10      ((((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['134'])).
% 0.92/1.10  thf('136', plain,
% 0.92/1.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.92/1.10      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.92/1.10  thf('137', plain,
% 0.92/1.10      (((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2)
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0))
% 0.92/1.10        | ((sk_C_2) = (k1_xboole_0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['135', '136'])).
% 0.92/1.10  thf('138', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.92/1.10      inference('simpl_trail', [status(thm)], ['96', '128'])).
% 0.92/1.10  thf('139', plain,
% 0.92/1.10      (((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2)
% 0.92/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 0.92/1.10  thf('140', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['8', '10'])).
% 0.92/1.10  thf('141', plain,
% 0.92/1.10      (![X3 : $i, X5 : $i]:
% 0.92/1.10         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.92/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.10  thf('142', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (~ (r2_hidden @ sk_A @ X0)
% 0.92/1.10          | (r1_tarski @ sk_B_1 @ X0)
% 0.92/1.10          | (r1_tarski @ sk_B_1 @ X0))),
% 0.92/1.10      inference('sup-', [status(thm)], ['140', '141'])).
% 0.92/1.10  thf('143', plain,
% 0.92/1.10      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.92/1.10      inference('simplify', [status(thm)], ['142'])).
% 0.92/1.10  thf('144', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['29', '55'])).
% 0.92/1.10  thf('145', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['143', '144'])).
% 0.92/1.10  thf('146', plain,
% 0.92/1.10      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.92/1.10      inference('sup-', [status(thm)], ['139', '145'])).
% 0.92/1.10  thf('147', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_tarski @ sk_B_1 @ X0) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['16', '19'])).
% 0.92/1.10  thf('148', plain, (![X66 : $i]: ((k1_xboole_0) != (k1_tarski @ X66))),
% 0.92/1.10      inference('demod', [status(thm)], ['113', '114'])).
% 0.92/1.10  thf('149', plain,
% 0.92/1.10      (![X0 : $i]: (((k1_xboole_0) != (sk_B_1)) | (r1_tarski @ sk_B_1 @ X0))),
% 0.92/1.10      inference('sup-', [status(thm)], ['147', '148'])).
% 0.92/1.10  thf('150', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.92/1.10      inference('clc', [status(thm)], ['146', '149'])).
% 0.92/1.10  thf('151', plain,
% 0.92/1.10      (![X14 : $i, X15 : $i]:
% 0.92/1.10         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.92/1.10      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.92/1.10  thf('152', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.92/1.10      inference('sup-', [status(thm)], ['150', '151'])).
% 0.92/1.10  thf('153', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_C_2))),
% 0.92/1.10      inference('sup+', [status(thm)], ['57', '152'])).
% 0.92/1.10  thf('154', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.92/1.10      inference('simpl_trail', [status(thm)], ['31', '54'])).
% 0.92/1.10  thf('155', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['29', '55'])).
% 0.92/1.10  thf('156', plain, (((sk_C_2) != (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.92/1.10      inference('demod', [status(thm)], ['154', '155'])).
% 0.92/1.10  thf('157', plain, ($false),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['153', '156'])).
% 0.92/1.10  
% 0.92/1.10  % SZS output end Refutation
% 0.92/1.10  
% 0.92/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
