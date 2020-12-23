%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DYglauUZah

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:34 EST 2020

% Result     : Theorem 30.33s
% Output     : Refutation 30.33s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 602 expanded)
%              Number of leaves         :   20 ( 179 expanded)
%              Depth                    :   26
%              Number of atoms          : 1070 (6901 expanded)
%              Number of equality atoms :  101 ( 849 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('2',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X37 @ X39 ) @ ( k3_xboole_0 @ X38 @ X40 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X37 @ X39 ) @ ( k3_xboole_0 @ X38 @ X40 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_C_2 ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_2 ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X37 @ X39 ) @ ( k3_xboole_0 @ X38 @ X40 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf('21',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_D_1 @ sk_B )
    | ( sk_D_1 = sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ( X18 != X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X19: $i] :
      ( r1_tarski @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X32 @ X30 ) @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X28 @ X27 ) @ ( k2_zfmisc_1 @ X29 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ( sk_A = sk_C_2 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('51',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','27'])).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k3_xboole_0 @ X0 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ X0 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('56',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['49'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_D_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('64',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X37 @ X39 ) @ ( k3_xboole_0 @ X38 @ X40 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X37 @ X39 ) @ ( k3_xboole_0 @ X38 @ X40 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ X1 ) @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('72',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('76',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ X1 ) @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('81',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_D_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('83',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ),
    inference('sup+',[status(thm)],['74','83'])).

thf('85',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X28 @ X27 ) @ ( k2_zfmisc_1 @ X29 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
    | ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X19: $i] :
      ( r1_tarski @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('92',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_A = sk_C_2 ),
    inference(demod,[status(thm)],['48','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','93'])).

thf('95',plain,(
    r1_tarski @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['32','94'])).

thf('96',plain,(
    sk_D_1 = sk_B ),
    inference(demod,[status(thm)],['30','95'])).

thf('97',plain,
    ( ( sk_A != sk_C_2 )
    | ( sk_B != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,(
    sk_A = sk_C_2 ),
    inference(demod,[status(thm)],['48','92'])).

thf('100',plain,
    ( ( sk_A != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['97'])).

thf('101',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_A = sk_C_2 ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( sk_B != sk_D_1 )
    | ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['97'])).

thf('104',plain,(
    sk_B != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_B != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['98','104'])).

thf('106',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['96','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DYglauUZah
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 30.33/30.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 30.33/30.57  % Solved by: fo/fo7.sh
% 30.33/30.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.33/30.57  % done 13401 iterations in 30.106s
% 30.33/30.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 30.33/30.57  % SZS output start Refutation
% 30.33/30.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 30.33/30.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.33/30.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 30.33/30.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 30.33/30.57  thf(sk_B_type, type, sk_B: $i).
% 30.33/30.57  thf(sk_A_type, type, sk_A: $i).
% 30.33/30.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 30.33/30.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 30.33/30.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 30.33/30.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 30.33/30.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 30.33/30.57  thf(idempotence_k3_xboole_0, axiom,
% 30.33/30.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 30.33/30.57  thf('0', plain, (![X15 : $i]: ((k3_xboole_0 @ X15 @ X15) = (X15))),
% 30.33/30.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 30.33/30.57  thf('1', plain, (![X15 : $i]: ((k3_xboole_0 @ X15 @ X15) = (X15))),
% 30.33/30.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 30.33/30.57  thf(t134_zfmisc_1, conjecture,
% 30.33/30.57    (![A:$i,B:$i,C:$i,D:$i]:
% 30.33/30.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 30.33/30.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.33/30.57         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 30.33/30.57  thf(zf_stmt_0, negated_conjecture,
% 30.33/30.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 30.33/30.57        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 30.33/30.57          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.33/30.57            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 30.33/30.57    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 30.33/30.57  thf('2', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf(t123_zfmisc_1, axiom,
% 30.33/30.57    (![A:$i,B:$i,C:$i,D:$i]:
% 30.33/30.57     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 30.33/30.57       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 30.33/30.57  thf('3', plain,
% 30.33/30.57      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ X37 @ X39) @ (k3_xboole_0 @ X38 @ X40))
% 30.33/30.57           = (k3_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38) @ 
% 30.33/30.57              (k2_zfmisc_1 @ X39 @ X40)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 30.33/30.57  thf('4', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 30.33/30.57           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 30.33/30.57              (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 30.33/30.57      inference('sup+', [status(thm)], ['2', '3'])).
% 30.33/30.57  thf('5', plain,
% 30.33/30.57      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ X37 @ X39) @ (k3_xboole_0 @ X38 @ X40))
% 30.33/30.57           = (k3_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38) @ 
% 30.33/30.57              (k2_zfmisc_1 @ X39 @ X40)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 30.33/30.57  thf('6', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 30.33/30.57           = (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_C_2) @ 
% 30.33/30.57              (k3_xboole_0 @ X0 @ sk_D_1)))),
% 30.33/30.57      inference('demod', [status(thm)], ['4', '5'])).
% 30.33/30.57  thf('7', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 30.33/30.57           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_2) @ 
% 30.33/30.57              (k3_xboole_0 @ X0 @ sk_D_1)))),
% 30.33/30.57      inference('sup+', [status(thm)], ['1', '6'])).
% 30.33/30.57  thf(commutativity_k3_xboole_0, axiom,
% 30.33/30.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 30.33/30.57  thf('8', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 30.33/30.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 30.33/30.57  thf('9', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 30.33/30.57           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ 
% 30.33/30.57              (k3_xboole_0 @ X0 @ sk_D_1)))),
% 30.33/30.57      inference('demod', [status(thm)], ['7', '8'])).
% 30.33/30.57  thf('10', plain,
% 30.33/30.57      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ X37 @ X39) @ (k3_xboole_0 @ X38 @ X40))
% 30.33/30.57           = (k3_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38) @ 
% 30.33/30.57              (k2_zfmisc_1 @ X39 @ X40)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 30.33/30.57  thf(d3_tarski, axiom,
% 30.33/30.57    (![A:$i,B:$i]:
% 30.33/30.57     ( ( r1_tarski @ A @ B ) <=>
% 30.33/30.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 30.33/30.57  thf('11', plain,
% 30.33/30.57      (![X3 : $i, X5 : $i]:
% 30.33/30.57         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 30.33/30.57      inference('cnf', [status(esa)], [d3_tarski])).
% 30.33/30.57  thf(d4_xboole_0, axiom,
% 30.33/30.57    (![A:$i,B:$i,C:$i]:
% 30.33/30.57     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 30.33/30.57       ( ![D:$i]:
% 30.33/30.57         ( ( r2_hidden @ D @ C ) <=>
% 30.33/30.57           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 30.33/30.57  thf('12', plain,
% 30.33/30.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 30.33/30.57         (~ (r2_hidden @ X10 @ X9)
% 30.33/30.57          | (r2_hidden @ X10 @ X8)
% 30.33/30.57          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 30.33/30.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 30.33/30.57  thf('13', plain,
% 30.33/30.57      (![X7 : $i, X8 : $i, X10 : $i]:
% 30.33/30.57         ((r2_hidden @ X10 @ X8)
% 30.33/30.57          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 30.33/30.57      inference('simplify', [status(thm)], ['12'])).
% 30.33/30.57  thf('14', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.33/30.57         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 30.33/30.57          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 30.33/30.57      inference('sup-', [status(thm)], ['11', '13'])).
% 30.33/30.57  thf('15', plain,
% 30.33/30.57      (![X3 : $i, X5 : $i]:
% 30.33/30.57         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 30.33/30.57      inference('cnf', [status(esa)], [d3_tarski])).
% 30.33/30.57  thf('16', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 30.33/30.57          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 30.33/30.57      inference('sup-', [status(thm)], ['14', '15'])).
% 30.33/30.57  thf('17', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 30.33/30.57      inference('simplify', [status(thm)], ['16'])).
% 30.33/30.57  thf('18', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 30.33/30.57         (r1_tarski @ 
% 30.33/30.57          (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 30.33/30.57          (k2_zfmisc_1 @ X2 @ X0))),
% 30.33/30.57      inference('sup+', [status(thm)], ['10', '17'])).
% 30.33/30.57  thf('19', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (r1_tarski @ (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 30.33/30.57          (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 30.33/30.57      inference('sup+', [status(thm)], ['9', '18'])).
% 30.33/30.57  thf('20', plain,
% 30.33/30.57      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 30.33/30.57      inference('sup+', [status(thm)], ['0', '19'])).
% 30.33/30.57  thf('21', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('22', plain,
% 30.33/30.57      ((r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 30.33/30.57        (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 30.33/30.57      inference('demod', [status(thm)], ['20', '21'])).
% 30.33/30.57  thf('23', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf(t117_zfmisc_1, axiom,
% 30.33/30.57    (![A:$i,B:$i,C:$i]:
% 30.33/30.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 30.33/30.57          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 30.33/30.57            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 30.33/30.57          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 30.33/30.57  thf('24', plain,
% 30.33/30.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.33/30.57         (((X27) = (k1_xboole_0))
% 30.33/30.57          | (r1_tarski @ X28 @ X29)
% 30.33/30.57          | ~ (r1_tarski @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 30.33/30.57               (k2_zfmisc_1 @ X27 @ X29)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 30.33/30.57  thf('25', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 30.33/30.57             (k2_zfmisc_1 @ sk_A @ X0))
% 30.33/30.57          | (r1_tarski @ sk_B @ X0)
% 30.33/30.57          | ((sk_A) = (k1_xboole_0)))),
% 30.33/30.57      inference('sup-', [status(thm)], ['23', '24'])).
% 30.33/30.57  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('27', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 30.33/30.57             (k2_zfmisc_1 @ sk_A @ X0))
% 30.33/30.57          | (r1_tarski @ sk_B @ X0))),
% 30.33/30.57      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 30.33/30.57  thf('28', plain, ((r1_tarski @ sk_B @ sk_D_1)),
% 30.33/30.57      inference('sup-', [status(thm)], ['22', '27'])).
% 30.33/30.57  thf(d10_xboole_0, axiom,
% 30.33/30.57    (![A:$i,B:$i]:
% 30.33/30.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 30.33/30.57  thf('29', plain,
% 30.33/30.57      (![X18 : $i, X20 : $i]:
% 30.33/30.57         (((X18) = (X20))
% 30.33/30.57          | ~ (r1_tarski @ X20 @ X18)
% 30.33/30.57          | ~ (r1_tarski @ X18 @ X20))),
% 30.33/30.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.33/30.57  thf('30', plain, ((~ (r1_tarski @ sk_D_1 @ sk_B) | ((sk_D_1) = (sk_B)))),
% 30.33/30.57      inference('sup-', [status(thm)], ['28', '29'])).
% 30.33/30.57  thf('31', plain,
% 30.33/30.57      (![X18 : $i, X19 : $i]: ((r1_tarski @ X18 @ X19) | ((X18) != (X19)))),
% 30.33/30.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.33/30.57  thf('32', plain, (![X19 : $i]: (r1_tarski @ X19 @ X19)),
% 30.33/30.57      inference('simplify', [status(thm)], ['31'])).
% 30.33/30.57  thf('33', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('34', plain,
% 30.33/30.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.33/30.57         (((X27) = (k1_xboole_0))
% 30.33/30.57          | (r1_tarski @ X28 @ X29)
% 30.33/30.57          | ~ (r1_tarski @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 30.33/30.57               (k2_zfmisc_1 @ X27 @ X29)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 30.33/30.57  thf('35', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 30.33/30.57             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 30.33/30.57          | (r1_tarski @ X0 @ sk_B)
% 30.33/30.57          | ((sk_A) = (k1_xboole_0)))),
% 30.33/30.57      inference('sup-', [status(thm)], ['33', '34'])).
% 30.33/30.57  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('37', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 30.33/30.57             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 30.33/30.57          | (r1_tarski @ X0 @ sk_B))),
% 30.33/30.57      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 30.33/30.57  thf('38', plain, ((r1_tarski @ sk_B @ sk_D_1)),
% 30.33/30.57      inference('sup-', [status(thm)], ['22', '27'])).
% 30.33/30.57  thf(t118_zfmisc_1, axiom,
% 30.33/30.57    (![A:$i,B:$i,C:$i]:
% 30.33/30.57     ( ( r1_tarski @ A @ B ) =>
% 30.33/30.57       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 30.33/30.57         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 30.33/30.57  thf('39', plain,
% 30.33/30.57      (![X30 : $i, X31 : $i, X32 : $i]:
% 30.33/30.57         (~ (r1_tarski @ X30 @ X31)
% 30.33/30.57          | (r1_tarski @ (k2_zfmisc_1 @ X32 @ X30) @ (k2_zfmisc_1 @ X32 @ X31)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 30.33/30.57  thf('40', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D_1))),
% 30.33/30.57      inference('sup-', [status(thm)], ['38', '39'])).
% 30.33/30.57  thf('41', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('42', plain,
% 30.33/30.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.33/30.57         (((X27) = (k1_xboole_0))
% 30.33/30.57          | (r1_tarski @ X28 @ X29)
% 30.33/30.57          | ~ (r1_tarski @ (k2_zfmisc_1 @ X28 @ X27) @ 
% 30.33/30.57               (k2_zfmisc_1 @ X29 @ X27)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 30.33/30.57  thf('43', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 30.33/30.57             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 30.33/30.57          | (r1_tarski @ X0 @ sk_A)
% 30.33/30.57          | ((sk_B) = (k1_xboole_0)))),
% 30.33/30.57      inference('sup-', [status(thm)], ['41', '42'])).
% 30.33/30.57  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('45', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 30.33/30.57             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 30.33/30.57          | (r1_tarski @ X0 @ sk_A))),
% 30.33/30.57      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 30.33/30.57  thf('46', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 30.33/30.57      inference('sup-', [status(thm)], ['40', '45'])).
% 30.33/30.57  thf('47', plain,
% 30.33/30.57      (![X18 : $i, X20 : $i]:
% 30.33/30.57         (((X18) = (X20))
% 30.33/30.57          | ~ (r1_tarski @ X20 @ X18)
% 30.33/30.57          | ~ (r1_tarski @ X18 @ X20))),
% 30.33/30.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.33/30.57  thf('48', plain, ((~ (r1_tarski @ sk_A @ sk_C_2) | ((sk_A) = (sk_C_2)))),
% 30.33/30.57      inference('sup-', [status(thm)], ['46', '47'])).
% 30.33/30.57  thf('49', plain,
% 30.33/30.57      (![X7 : $i, X8 : $i, X11 : $i]:
% 30.33/30.57         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 30.33/30.57          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 30.33/30.57          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 30.33/30.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 30.33/30.57  thf('50', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 30.33/30.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 30.33/30.57      inference('eq_fact', [status(thm)], ['49'])).
% 30.33/30.57  thf('51', plain, ((r1_tarski @ sk_B @ sk_D_1)),
% 30.33/30.57      inference('sup-', [status(thm)], ['22', '27'])).
% 30.33/30.57  thf('52', plain,
% 30.33/30.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 30.33/30.57         (~ (r2_hidden @ X2 @ X3)
% 30.33/30.57          | (r2_hidden @ X2 @ X4)
% 30.33/30.57          | ~ (r1_tarski @ X3 @ X4))),
% 30.33/30.57      inference('cnf', [status(esa)], [d3_tarski])).
% 30.33/30.57  thf('53', plain,
% 30.33/30.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 30.33/30.57      inference('sup-', [status(thm)], ['51', '52'])).
% 30.33/30.57  thf('54', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (((sk_B) = (k3_xboole_0 @ X0 @ sk_B))
% 30.33/30.57          | (r2_hidden @ (sk_D @ sk_B @ sk_B @ X0) @ sk_D_1))),
% 30.33/30.57      inference('sup-', [status(thm)], ['50', '53'])).
% 30.33/30.57  thf('55', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 30.33/30.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 30.33/30.57      inference('eq_fact', [status(thm)], ['49'])).
% 30.33/30.57  thf('56', plain,
% 30.33/30.57      (![X7 : $i, X8 : $i, X11 : $i]:
% 30.33/30.57         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 30.33/30.57          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 30.33/30.57          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 30.33/30.57          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 30.33/30.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 30.33/30.57  thf('57', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 30.33/30.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 30.33/30.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 30.33/30.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 30.33/30.57      inference('sup-', [status(thm)], ['55', '56'])).
% 30.33/30.57  thf('58', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 30.33/30.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 30.33/30.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 30.33/30.57      inference('simplify', [status(thm)], ['57'])).
% 30.33/30.57  thf('59', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 30.33/30.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 30.33/30.57      inference('eq_fact', [status(thm)], ['49'])).
% 30.33/30.57  thf('60', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 30.33/30.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 30.33/30.57      inference('clc', [status(thm)], ['58', '59'])).
% 30.33/30.57  thf('61', plain,
% 30.33/30.57      ((((sk_B) = (k3_xboole_0 @ sk_D_1 @ sk_B))
% 30.33/30.57        | ((sk_B) = (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 30.33/30.57      inference('sup-', [status(thm)], ['54', '60'])).
% 30.33/30.57  thf('62', plain, (((sk_B) = (k3_xboole_0 @ sk_D_1 @ sk_B))),
% 30.33/30.57      inference('simplify', [status(thm)], ['61'])).
% 30.33/30.57  thf('63', plain, (![X15 : $i]: ((k3_xboole_0 @ X15 @ X15) = (X15))),
% 30.33/30.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 30.33/30.57  thf('64', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('65', plain,
% 30.33/30.57      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ X37 @ X39) @ (k3_xboole_0 @ X38 @ X40))
% 30.33/30.57           = (k3_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38) @ 
% 30.33/30.57              (k2_zfmisc_1 @ X39 @ X40)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 30.33/30.57  thf('66', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 30.33/30.57           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 30.33/30.57              (k2_zfmisc_1 @ X1 @ X0)))),
% 30.33/30.57      inference('sup+', [status(thm)], ['64', '65'])).
% 30.33/30.57  thf('67', plain,
% 30.33/30.57      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ X37 @ X39) @ (k3_xboole_0 @ X38 @ X40))
% 30.33/30.57           = (k3_xboole_0 @ (k2_zfmisc_1 @ X37 @ X38) @ 
% 30.33/30.57              (k2_zfmisc_1 @ X39 @ X40)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 30.33/30.57  thf('68', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 30.33/30.57           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ X1) @ 
% 30.33/30.57              (k3_xboole_0 @ sk_D_1 @ X0)))),
% 30.33/30.57      inference('demod', [status(thm)], ['66', '67'])).
% 30.33/30.57  thf('69', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 30.33/30.57           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ 
% 30.33/30.57              (k3_xboole_0 @ sk_D_1 @ X0)))),
% 30.33/30.57      inference('sup+', [status(thm)], ['63', '68'])).
% 30.33/30.57  thf('70', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_B))
% 30.33/30.57         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ sk_B))),
% 30.33/30.57      inference('sup+', [status(thm)], ['62', '69'])).
% 30.33/30.57  thf('71', plain, (![X15 : $i]: ((k3_xboole_0 @ X15 @ X15) = (X15))),
% 30.33/30.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 30.33/30.57  thf('72', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 30.33/30.57         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ sk_B))),
% 30.33/30.57      inference('demod', [status(thm)], ['70', '71'])).
% 30.33/30.57  thf('73', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('74', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_C_2 @ sk_D_1)
% 30.33/30.57         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ sk_B))),
% 30.33/30.57      inference('demod', [status(thm)], ['72', '73'])).
% 30.33/30.57  thf('75', plain, (![X15 : $i]: ((k3_xboole_0 @ X15 @ X15) = (X15))),
% 30.33/30.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 30.33/30.57  thf('76', plain, (![X15 : $i]: ((k3_xboole_0 @ X15 @ X15) = (X15))),
% 30.33/30.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 30.33/30.57  thf('77', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 30.33/30.57           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ X1) @ 
% 30.33/30.57              (k3_xboole_0 @ sk_D_1 @ X0)))),
% 30.33/30.57      inference('demod', [status(thm)], ['66', '67'])).
% 30.33/30.57  thf('78', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 30.33/30.57           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ X0) @ 
% 30.33/30.57              (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 30.33/30.57      inference('sup+', [status(thm)], ['76', '77'])).
% 30.33/30.57  thf('79', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_2) @ sk_B)
% 30.33/30.57         = (k2_zfmisc_1 @ sk_C_2 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 30.33/30.57      inference('sup+', [status(thm)], ['75', '78'])).
% 30.33/30.57  thf('80', plain,
% 30.33/30.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 30.33/30.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 30.33/30.57  thf('81', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)
% 30.33/30.57         = (k2_zfmisc_1 @ sk_C_2 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 30.33/30.57      inference('demod', [status(thm)], ['79', '80'])).
% 30.33/30.57  thf('82', plain, (((sk_B) = (k3_xboole_0 @ sk_D_1 @ sk_B))),
% 30.33/30.57      inference('simplify', [status(thm)], ['61'])).
% 30.33/30.57  thf('83', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)
% 30.33/30.57         = (k2_zfmisc_1 @ sk_C_2 @ sk_B))),
% 30.33/30.57      inference('demod', [status(thm)], ['81', '82'])).
% 30.33/30.57  thf('84', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_C_2 @ sk_D_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_B))),
% 30.33/30.57      inference('sup+', [status(thm)], ['74', '83'])).
% 30.33/30.57  thf('85', plain,
% 30.33/30.57      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('86', plain,
% 30.33/30.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.33/30.57         (((X27) = (k1_xboole_0))
% 30.33/30.57          | (r1_tarski @ X28 @ X29)
% 30.33/30.57          | ~ (r1_tarski @ (k2_zfmisc_1 @ X28 @ X27) @ 
% 30.33/30.57               (k2_zfmisc_1 @ X29 @ X27)))),
% 30.33/30.57      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 30.33/30.57  thf('87', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 30.33/30.57             (k2_zfmisc_1 @ X0 @ sk_B))
% 30.33/30.57          | (r1_tarski @ sk_A @ X0)
% 30.33/30.57          | ((sk_B) = (k1_xboole_0)))),
% 30.33/30.57      inference('sup-', [status(thm)], ['85', '86'])).
% 30.33/30.57  thf('88', plain, (((sk_B) != (k1_xboole_0))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('89', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 30.33/30.57             (k2_zfmisc_1 @ X0 @ sk_B))
% 30.33/30.57          | (r1_tarski @ sk_A @ X0))),
% 30.33/30.57      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 30.33/30.57  thf('90', plain,
% 30.33/30.57      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 30.33/30.57           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 30.33/30.57        | (r1_tarski @ sk_A @ sk_C_2))),
% 30.33/30.57      inference('sup-', [status(thm)], ['84', '89'])).
% 30.33/30.57  thf('91', plain, (![X19 : $i]: (r1_tarski @ X19 @ X19)),
% 30.33/30.57      inference('simplify', [status(thm)], ['31'])).
% 30.33/30.57  thf('92', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 30.33/30.57      inference('demod', [status(thm)], ['90', '91'])).
% 30.33/30.57  thf('93', plain, (((sk_A) = (sk_C_2))),
% 30.33/30.57      inference('demod', [status(thm)], ['48', '92'])).
% 30.33/30.57  thf('94', plain,
% 30.33/30.57      (![X0 : $i]:
% 30.33/30.57         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ X0) @ 
% 30.33/30.57             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 30.33/30.57          | (r1_tarski @ X0 @ sk_B))),
% 30.33/30.57      inference('demod', [status(thm)], ['37', '93'])).
% 30.33/30.57  thf('95', plain, ((r1_tarski @ sk_D_1 @ sk_B)),
% 30.33/30.57      inference('sup-', [status(thm)], ['32', '94'])).
% 30.33/30.57  thf('96', plain, (((sk_D_1) = (sk_B))),
% 30.33/30.57      inference('demod', [status(thm)], ['30', '95'])).
% 30.33/30.57  thf('97', plain, ((((sk_A) != (sk_C_2)) | ((sk_B) != (sk_D_1)))),
% 30.33/30.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.33/30.57  thf('98', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 30.33/30.57      inference('split', [status(esa)], ['97'])).
% 30.33/30.57  thf('99', plain, (((sk_A) = (sk_C_2))),
% 30.33/30.57      inference('demod', [status(thm)], ['48', '92'])).
% 30.33/30.57  thf('100', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 30.33/30.57      inference('split', [status(esa)], ['97'])).
% 30.33/30.57  thf('101', plain, ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 30.33/30.57      inference('sup-', [status(thm)], ['99', '100'])).
% 30.33/30.57  thf('102', plain, ((((sk_A) = (sk_C_2)))),
% 30.33/30.57      inference('simplify', [status(thm)], ['101'])).
% 30.33/30.57  thf('103', plain, (~ (((sk_B) = (sk_D_1))) | ~ (((sk_A) = (sk_C_2)))),
% 30.33/30.57      inference('split', [status(esa)], ['97'])).
% 30.33/30.57  thf('104', plain, (~ (((sk_B) = (sk_D_1)))),
% 30.33/30.57      inference('sat_resolution*', [status(thm)], ['102', '103'])).
% 30.33/30.57  thf('105', plain, (((sk_B) != (sk_D_1))),
% 30.33/30.57      inference('simpl_trail', [status(thm)], ['98', '104'])).
% 30.33/30.57  thf('106', plain, ($false),
% 30.33/30.57      inference('simplify_reflect-', [status(thm)], ['96', '105'])).
% 30.33/30.57  
% 30.33/30.57  % SZS output end Refutation
% 30.33/30.57  
% 30.33/30.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
