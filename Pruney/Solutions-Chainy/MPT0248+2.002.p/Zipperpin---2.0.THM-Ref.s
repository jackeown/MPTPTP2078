%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.icpYuWBvo8

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:18 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  179 (2514 expanded)
%              Number of leaves         :   24 ( 721 expanded)
%              Depth                    :   33
%              Number of atoms          : 1187 (25130 expanded)
%              Number of equality atoms :  178 (4185 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_2 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_2 @ X0 )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','31'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B_2 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 )
    | ( ( k2_xboole_0 @ sk_B_2 @ sk_C_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('47',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('50',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_C_2 != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_B_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['46','48','56'])).

thf('58',plain,(
    sk_B_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','57'])).

thf('59',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['43','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ sk_B_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','59'])).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('67',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('69',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_B_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('71',plain,
    ( ( r2_hidden @ sk_A @ sk_B_2 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('74',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('78',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('79',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( ( sk_B @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('85',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r1_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( ( k2_xboole_0 @ sk_B_2 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( ( k2_xboole_0 @ sk_B_2 @ k1_xboole_0 )
        = sk_C_2 )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('93',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('94',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('95',plain,
    ( ( ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B_2 )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('97',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('98',plain,
    ( ( k1_xboole_0
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('100',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ sk_B_2 @ k1_xboole_0 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('103',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_B_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k1_xboole_0
     != ( k2_xboole_0 @ k1_xboole_0 @ sk_B_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','103'])).

thf('105',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['95','104'])).

thf('106',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_B_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('115',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('116',plain,
    ( ( sk_B_2
     != ( k2_xboole_0 @ k1_xboole_0 @ sk_B_2 ) )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','118'])).

thf('120',plain,
    ( ! [X0: $i] :
        ~ ( v1_xboole_0 @ X0 )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( sk_C_2
      = ( k1_tarski @ sk_A ) )
    | ( sk_B_2
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','120'])).

thf('122',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('123',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','48','56','121','122'])).

thf('124',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['77','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','124'])).

thf('126',plain,(
    r2_hidden @ sk_A @ sk_B_2 ),
    inference('sup+',[status(thm)],['64','125'])).

thf('127',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( ( k2_xboole_0 @ sk_B_2 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('129',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( ( sk_C @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['127','134'])).

thf('136',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    r1_tarski @ sk_C_2 @ sk_B_2 ),
    inference('sup-',[status(thm)],['126','138'])).

thf('140',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('142',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['0','140','141'])).

thf('143',plain,(
    r1_tarski @ sk_C_2 @ sk_B_2 ),
    inference('sup-',[status(thm)],['126','138'])).

thf('144',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('145',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('147',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ sk_C_2 )
    = sk_B_2 ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','139'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('150',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B_2 )
    = sk_B_2 ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_2 ),
    inference(demod,[status(thm)],['142','150'])).

thf('152',plain,(
    sk_B_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','57'])).

thf('153',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['151','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.icpYuWBvo8
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:41:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 769 iterations in 0.304s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.58/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.77  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.58/0.77  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.77  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.58/0.77  thf(t43_zfmisc_1, conjecture,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.58/0.77          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.58/0.77          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.58/0.77          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.77        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.58/0.77             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.58/0.77             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.58/0.77             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.58/0.77  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t7_xboole_0, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.77          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.77  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(commutativity_k2_tarski, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (![X19 : $i, X20 : $i]:
% 0.58/0.77         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.58/0.77      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.58/0.77  thf(l51_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (![X36 : $i, X37 : $i]:
% 0.58/0.77         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 0.58/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.77  thf('5', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['3', '4'])).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X36 : $i, X37 : $i]:
% 0.58/0.77         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 0.58/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf(t7_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('8', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['7', '8'])).
% 0.58/0.77  thf('10', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.58/0.77      inference('sup+', [status(thm)], ['2', '9'])).
% 0.58/0.77  thf(d3_tarski, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X3 @ X4)
% 0.58/0.77          | (r2_hidden @ X3 @ X5)
% 0.58/0.77          | ~ (r1_tarski @ X4 @ X5))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.58/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0))
% 0.58/0.77        | (r2_hidden @ (sk_B_1 @ sk_C_2) @ (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['1', '12'])).
% 0.58/0.77  thf(d1_tarski, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X24 @ X23)
% 0.58/0.77          | ((X24) = (X21))
% 0.58/0.77          | ((X23) != (k1_tarski @ X21)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (![X21 : $i, X24 : $i]:
% 0.58/0.77         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['14'])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1 @ sk_C_2) = (sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['13', '15'])).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      (((r2_hidden @ sk_A @ sk_C_2)
% 0.58/0.77        | ((sk_C_2) = (k1_xboole_0))
% 0.58/0.77        | ((sk_C_2) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_C_2))),
% 0.58/0.77      inference('simplify', [status(thm)], ['18'])).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      (![X4 : $i, X6 : $i]:
% 0.58/0.77         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf('21', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.77  thf('23', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.58/0.77      inference('sup+', [status(thm)], ['21', '22'])).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X3 @ X4)
% 0.58/0.77          | (r2_hidden @ X3 @ X5)
% 0.58/0.77          | ~ (r1_tarski @ X4 @ X5))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf('25', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.58/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ sk_B_2 @ X0)
% 0.58/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['20', '25'])).
% 0.58/0.77  thf('27', plain,
% 0.58/0.77      (![X21 : $i, X24 : $i]:
% 0.58/0.77         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['14'])).
% 0.58/0.77  thf('28', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ sk_B_2 @ X0) | ((sk_C @ X0 @ sk_B_2) = (sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.77  thf('29', plain,
% 0.58/0.77      (![X4 : $i, X6 : $i]:
% 0.58/0.77         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (r2_hidden @ sk_A @ X0)
% 0.58/0.77          | (r1_tarski @ sk_B_2 @ X0)
% 0.58/0.77          | (r1_tarski @ sk_B_2 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.58/0.77  thf('31', plain,
% 0.58/0.77      (![X0 : $i]: ((r1_tarski @ sk_B_2 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['30'])).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0)) | (r1_tarski @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('sup-', [status(thm)], ['19', '31'])).
% 0.58/0.77  thf(t12_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.58/0.77  thf('33', plain,
% 0.58/0.77      (![X11 : $i, X12 : $i]:
% 0.58/0.77         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0))
% 0.58/0.77        | ((k2_xboole_0 @ sk_B_2 @ sk_C_2) = (sk_C_2)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('35', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (sk_C_2)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['34', '35'])).
% 0.58/0.77  thf('37', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('38', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.77  thf(d10_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.77  thf('39', plain,
% 0.58/0.77      (![X8 : $i, X10 : $i]:
% 0.58/0.77         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.58/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.77  thf('40', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.58/0.77          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.77  thf('41', plain,
% 0.58/0.77      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.58/0.77        | ((k2_xboole_0 @ sk_B_2 @ sk_C_2) = (sk_B_2)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['37', '40'])).
% 0.58/0.77  thf('42', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('43', plain,
% 0.58/0.77      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.58/0.77        | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.58/0.77      inference('demod', [status(thm)], ['41', '42'])).
% 0.58/0.77  thf('44', plain,
% 0.58/0.77      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('45', plain,
% 0.58/0.77      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.58/0.77         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('split', [status(esa)], ['44'])).
% 0.58/0.77  thf('46', plain,
% 0.58/0.77      (~ (((sk_B_2) = (k1_tarski @ sk_A))) | ~ (((sk_C_2) = (k1_xboole_0)))),
% 0.58/0.77      inference('split', [status(esa)], ['44'])).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('48', plain,
% 0.58/0.77      (~ (((sk_B_2) = (k1_tarski @ sk_A))) | 
% 0.58/0.77       ~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('split', [status(esa)], ['47'])).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (sk_C_2)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['34', '35'])).
% 0.58/0.77  thf('50', plain,
% 0.58/0.77      ((((sk_B_2) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('51', plain,
% 0.58/0.77      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('split', [status(esa)], ['50'])).
% 0.58/0.77  thf('52', plain,
% 0.58/0.77      (((((sk_C_2) != (sk_C_2)) | ((sk_C_2) = (k1_xboole_0))))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['49', '51'])).
% 0.58/0.77  thf('53', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.77  thf('54', plain,
% 0.58/0.77      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['44'])).
% 0.58/0.77  thf('55', plain,
% 0.58/0.77      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.58/0.77             ~ (((sk_C_2) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0))) | (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['55'])).
% 0.58/0.77  thf('57', plain, (~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sat_resolution*', [status(thm)], ['46', '48', '56'])).
% 0.58/0.77  thf('58', plain, (((sk_B_2) != (k1_tarski @ sk_A))),
% 0.58/0.77      inference('simpl_trail', [status(thm)], ['45', '57'])).
% 0.58/0.77  thf('59', plain, (~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['43', '58'])).
% 0.58/0.77  thf('60', plain,
% 0.58/0.77      ((~ (r1_tarski @ sk_C_2 @ sk_B_2) | ((sk_C_2) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['36', '59'])).
% 0.58/0.77  thf('61', plain,
% 0.58/0.77      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.77  thf('62', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.58/0.77      inference('simplify', [status(thm)], ['61'])).
% 0.58/0.77  thf('63', plain,
% 0.58/0.77      (![X11 : $i, X12 : $i]:
% 0.58/0.77         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.77  thf('64', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['62', '63'])).
% 0.58/0.77  thf('65', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.77  thf('66', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.58/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.77  thf('67', plain,
% 0.58/0.77      ((((sk_B_2) = (k1_xboole_0))
% 0.58/0.77        | (r2_hidden @ (sk_B_1 @ sk_B_2) @ (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.77  thf('68', plain,
% 0.58/0.77      (![X21 : $i, X24 : $i]:
% 0.58/0.77         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['14'])).
% 0.58/0.77  thf('69', plain,
% 0.58/0.77      ((((sk_B_2) = (k1_xboole_0)) | ((sk_B_1 @ sk_B_2) = (sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['67', '68'])).
% 0.58/0.77  thf('70', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.77  thf('71', plain,
% 0.58/0.77      (((r2_hidden @ sk_A @ sk_B_2)
% 0.58/0.77        | ((sk_B_2) = (k1_xboole_0))
% 0.58/0.77        | ((sk_B_2) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['69', '70'])).
% 0.58/0.77  thf('72', plain,
% 0.58/0.77      ((((sk_B_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_2))),
% 0.58/0.77      inference('simplify', [status(thm)], ['71'])).
% 0.58/0.77  thf('73', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.77  thf('74', plain,
% 0.58/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X3 @ X4)
% 0.58/0.77          | (r2_hidden @ X3 @ X5)
% 0.58/0.77          | ~ (r1_tarski @ X4 @ X5))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf('75', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['73', '74'])).
% 0.58/0.77  thf('76', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((sk_B_2) = (k1_xboole_0))
% 0.58/0.77          | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B_2 @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['72', '75'])).
% 0.58/0.77  thf('77', plain,
% 0.58/0.77      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['50'])).
% 0.58/0.77  thf('78', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.77  thf(d1_xboole_0, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.77  thf('79', plain,
% 0.58/0.77      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.77  thf('80', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.58/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.77  thf('81', plain,
% 0.58/0.77      (((v1_xboole_0 @ sk_C_2)
% 0.58/0.77        | (r2_hidden @ (sk_B @ sk_C_2) @ (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['79', '80'])).
% 0.58/0.77  thf('82', plain,
% 0.58/0.77      (![X21 : $i, X24 : $i]:
% 0.58/0.77         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['14'])).
% 0.58/0.77  thf('83', plain, (((v1_xboole_0 @ sk_C_2) | ((sk_B @ sk_C_2) = (sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['81', '82'])).
% 0.58/0.77  thf('84', plain,
% 0.58/0.77      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.77  thf('85', plain,
% 0.58/0.77      (((r2_hidden @ sk_A @ sk_C_2)
% 0.58/0.77        | (v1_xboole_0 @ sk_C_2)
% 0.58/0.77        | (v1_xboole_0 @ sk_C_2))),
% 0.58/0.77      inference('sup+', [status(thm)], ['83', '84'])).
% 0.58/0.77  thf('86', plain, (((v1_xboole_0 @ sk_C_2) | (r2_hidden @ sk_A @ sk_C_2))),
% 0.58/0.77      inference('simplify', [status(thm)], ['85'])).
% 0.58/0.77  thf('87', plain,
% 0.58/0.77      (![X0 : $i]: ((r1_tarski @ sk_B_2 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['30'])).
% 0.58/0.77  thf('88', plain, (((v1_xboole_0 @ sk_C_2) | (r1_tarski @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('sup-', [status(thm)], ['86', '87'])).
% 0.58/0.77  thf('89', plain,
% 0.58/0.77      (![X11 : $i, X12 : $i]:
% 0.58/0.77         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.77  thf('90', plain,
% 0.58/0.77      (((v1_xboole_0 @ sk_C_2) | ((k2_xboole_0 @ sk_B_2 @ sk_C_2) = (sk_C_2)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['88', '89'])).
% 0.58/0.77  thf('91', plain,
% 0.58/0.77      (((((k2_xboole_0 @ sk_B_2 @ k1_xboole_0) = (sk_C_2))
% 0.58/0.77         | (v1_xboole_0 @ sk_C_2))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['78', '90'])).
% 0.58/0.77  thf('92', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('93', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.77  thf('94', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.77  thf('95', plain,
% 0.58/0.77      (((((k2_xboole_0 @ k1_xboole_0 @ sk_B_2) = (k1_xboole_0))
% 0.58/0.77         | (v1_xboole_0 @ k1_xboole_0)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.58/0.77  thf('96', plain,
% 0.58/0.77      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('split', [status(esa)], ['50'])).
% 0.58/0.77  thf('97', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.77  thf('98', plain,
% 0.58/0.77      ((((k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('demod', [status(thm)], ['96', '97'])).
% 0.58/0.77  thf('99', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['52'])).
% 0.58/0.77  thf('100', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('101', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ k1_xboole_0)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['99', '100'])).
% 0.58/0.77  thf('102', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('103', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_B_2)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('demod', [status(thm)], ['101', '102'])).
% 0.58/0.77  thf('104', plain,
% 0.58/0.77      ((((k1_xboole_0) != (k2_xboole_0 @ k1_xboole_0 @ sk_B_2)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('demod', [status(thm)], ['98', '103'])).
% 0.58/0.77  thf('105', plain,
% 0.58/0.77      (((v1_xboole_0 @ k1_xboole_0)) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['95', '104'])).
% 0.58/0.77  thf('106', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.77  thf('107', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.77  thf('108', plain,
% 0.58/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['106', '107'])).
% 0.58/0.77  thf('109', plain,
% 0.58/0.77      (![X4 : $i, X6 : $i]:
% 0.58/0.77         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf('110', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.77  thf('111', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['109', '110'])).
% 0.58/0.77  thf('112', plain,
% 0.58/0.77      (![X11 : $i, X12 : $i]:
% 0.58/0.77         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.77  thf('113', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['111', '112'])).
% 0.58/0.77  thf('114', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_B_2)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('demod', [status(thm)], ['101', '102'])).
% 0.58/0.77  thf('115', plain,
% 0.58/0.77      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.58/0.77         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('split', [status(esa)], ['44'])).
% 0.58/0.77  thf('116', plain,
% 0.58/0.77      ((((sk_B_2) != (k2_xboole_0 @ k1_xboole_0 @ sk_B_2)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.58/0.77             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['114', '115'])).
% 0.58/0.77  thf('117', plain,
% 0.58/0.77      (((((sk_B_2) != (sk_B_2)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.58/0.77             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['113', '116'])).
% 0.58/0.77  thf('118', plain,
% 0.58/0.77      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.58/0.77             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['117'])).
% 0.58/0.77  thf('119', plain,
% 0.58/0.77      ((![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0)))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.58/0.77             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['108', '118'])).
% 0.58/0.77  thf('120', plain,
% 0.58/0.77      ((![X0 : $i]: ~ (v1_xboole_0 @ X0))
% 0.58/0.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.58/0.77             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['119'])).
% 0.58/0.77  thf('121', plain,
% 0.58/0.77      ((((sk_C_2) = (k1_tarski @ sk_A))) | (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['105', '120'])).
% 0.58/0.77  thf('122', plain,
% 0.58/0.77      (~ (((sk_B_2) = (k1_xboole_0))) | ~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('split', [status(esa)], ['50'])).
% 0.58/0.77  thf('123', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.58/0.77      inference('sat_resolution*', [status(thm)],
% 0.58/0.77                ['46', '48', '56', '121', '122'])).
% 0.58/0.77  thf('124', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.58/0.77      inference('simpl_trail', [status(thm)], ['77', '123'])).
% 0.58/0.77  thf('125', plain,
% 0.58/0.77      (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B_2 @ X0))),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['76', '124'])).
% 0.58/0.77  thf('126', plain, ((r2_hidden @ sk_A @ sk_B_2)),
% 0.58/0.77      inference('sup+', [status(thm)], ['64', '125'])).
% 0.58/0.77  thf('127', plain,
% 0.58/0.77      (![X4 : $i, X6 : $i]:
% 0.58/0.77         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf('128', plain,
% 0.58/0.77      (((v1_xboole_0 @ sk_C_2) | ((k2_xboole_0 @ sk_B_2 @ sk_C_2) = (sk_C_2)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['88', '89'])).
% 0.58/0.77  thf('129', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('130', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (sk_C_2)) | (v1_xboole_0 @ sk_C_2))),
% 0.58/0.77      inference('sup+', [status(thm)], ['128', '129'])).
% 0.58/0.77  thf('131', plain,
% 0.58/0.77      (![X21 : $i, X24 : $i]:
% 0.58/0.77         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['14'])).
% 0.58/0.77  thf('132', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X0 @ sk_C_2)
% 0.58/0.77          | (v1_xboole_0 @ sk_C_2)
% 0.58/0.77          | ((X0) = (sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['130', '131'])).
% 0.58/0.77  thf('133', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.77  thf('134', plain,
% 0.58/0.77      (![X0 : $i]: (((X0) = (sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.58/0.77      inference('clc', [status(thm)], ['132', '133'])).
% 0.58/0.77  thf('135', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ sk_C_2 @ X0) | ((sk_C @ X0 @ sk_C_2) = (sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['127', '134'])).
% 0.58/0.77  thf('136', plain,
% 0.58/0.77      (![X4 : $i, X6 : $i]:
% 0.58/0.77         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf('137', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (r2_hidden @ sk_A @ X0)
% 0.58/0.77          | (r1_tarski @ sk_C_2 @ X0)
% 0.58/0.77          | (r1_tarski @ sk_C_2 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['135', '136'])).
% 0.58/0.77  thf('138', plain,
% 0.58/0.77      (![X0 : $i]: ((r1_tarski @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['137'])).
% 0.58/0.77  thf('139', plain, ((r1_tarski @ sk_C_2 @ sk_B_2)),
% 0.58/0.77      inference('sup-', [status(thm)], ['126', '138'])).
% 0.58/0.77  thf('140', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['60', '139'])).
% 0.58/0.77  thf('141', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('142', plain,
% 0.58/0.77      (((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_B_2))),
% 0.58/0.77      inference('demod', [status(thm)], ['0', '140', '141'])).
% 0.58/0.77  thf('143', plain, ((r1_tarski @ sk_C_2 @ sk_B_2)),
% 0.58/0.77      inference('sup-', [status(thm)], ['126', '138'])).
% 0.58/0.77  thf('144', plain,
% 0.58/0.77      (![X11 : $i, X12 : $i]:
% 0.58/0.77         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.77  thf('145', plain, (((k2_xboole_0 @ sk_C_2 @ sk_B_2) = (sk_B_2))),
% 0.58/0.77      inference('sup-', [status(thm)], ['143', '144'])).
% 0.58/0.77  thf('146', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('147', plain, (((k2_xboole_0 @ sk_B_2 @ sk_C_2) = (sk_B_2))),
% 0.58/0.77      inference('demod', [status(thm)], ['145', '146'])).
% 0.58/0.77  thf('148', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['60', '139'])).
% 0.58/0.77  thf('149', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('150', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_B_2) = (sk_B_2))),
% 0.58/0.77      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.58/0.77  thf('151', plain, (((k1_tarski @ sk_A) = (sk_B_2))),
% 0.58/0.77      inference('demod', [status(thm)], ['142', '150'])).
% 0.58/0.77  thf('152', plain, (((sk_B_2) != (k1_tarski @ sk_A))),
% 0.58/0.77      inference('simpl_trail', [status(thm)], ['45', '57'])).
% 0.58/0.77  thf('153', plain, ($false),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['151', '152'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
