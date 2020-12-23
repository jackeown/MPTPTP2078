%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CvsNwuXC08

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:20 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 288 expanded)
%              Number of leaves         :   29 (  90 expanded)
%              Depth                    :   17
%              Number of atoms          :  722 (2969 expanded)
%              Number of equality atoms :   41 (  94 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t58_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( r2_hidden @ B @ A )
       => ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
             => ( r2_hidden @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( r2_hidden @ B @ A )
         => ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ C )
               => ( r2_hidden @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_setfam_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_D @ sk_C_3 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D @ sk_C_3 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k6_setfam_1 @ X31 @ X30 )
        = ( k1_setfam_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('7',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_3 )
    = ( k1_setfam_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X27 @ X26 )
        = ( k6_setfam_1 @ X27 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_3 )
      = ( k6_setfam_1 @ sk_A @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_C_3 )
      | ( r2_hidden @ sk_B_1 @ X39 )
      | ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k6_setfam_1 @ sk_A @ sk_C_3 ) )
      | ( sk_C_3 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_3 ) )
      | ( sk_C_3 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_D @ sk_C_3 )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference(split,[status(esa)],['3'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_3 ) @ sk_D )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_D )
        | ~ ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_C_3 ) ) )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C_3 = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ sk_D ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
      & ( r2_hidden @ sk_D @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( sk_C_3 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
      & ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
      & ( r2_hidden @ sk_D @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_D @ sk_C_3 )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference(split,[status(esa)],['3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ sk_C_3 )
   <= ( r2_hidden @ sk_D @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
      & ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
      & ( r2_hidden @ sk_D @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ ( k1_tarski @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('34',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ X14 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X20 )
      | ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X19 @ ( k1_tarski @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ~ ( r2_hidden @ X20 @ ( k4_xboole_0 @ X19 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_D @ sk_C_3 )
    | ( r2_hidden @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['26','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','41'])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X38 @ X37 ) @ X37 )
      | ( r1_tarski @ X38 @ ( k1_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('44',plain,
    ( ! [X39: $i] :
        ( ~ ( r2_hidden @ X39 @ sk_C_3 )
        | ( r2_hidden @ sk_B_1 @ X39 ) )
   <= ! [X39: $i] :
        ( ~ ( r2_hidden @ X39 @ sk_C_3 )
        | ( r2_hidden @ sk_B_1 @ X39 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_C_3 ) )
        | ( sk_C_3 = k1_xboole_0 )
        | ( r2_hidden @ sk_B_1 @ ( sk_C_2 @ X0 @ sk_C_3 ) ) )
   <= ! [X39: $i] :
        ( ~ ( r2_hidden @ X39 @ sk_C_3 )
        | ( r2_hidden @ sk_B_1 @ X39 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ! [X39: $i] :
        ( ~ ( r2_hidden @ X39 @ sk_C_3 )
        | ( r2_hidden @ sk_B_1 @ X39 ) )
    | ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('47',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_C_3 )
      | ( r2_hidden @ sk_B_1 @ X39 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','40','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_C_3 ) )
      | ( sk_C_3 = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ ( sk_C_2 @ X0 @ sk_C_3 ) ) ) ),
    inference(simpl_trail,[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_C_3 = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_C_3 ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( sk_C_2 @ X0 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X38 @ ( sk_C_2 @ X38 @ X37 ) )
      | ( r1_tarski @ X38 @ ( k1_setfam_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('52',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_setfam_1 @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_setfam_1 @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_setfam_1 @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ ( k1_tarski @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('55',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_3 )
      = ( k6_setfam_1 @ sk_A @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( ~ ( r2_hidden @ sk_B_1 @ ( k6_setfam_1 @ sk_A @ sk_C_3 ) )
      | ( sk_C_3 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_3 )
    = ( k1_setfam_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('60',plain,
    ( ( ~ ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_3 ) )
      | ( sk_C_3 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','40'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['60','61'])).

thf('63',plain,(
    sk_C_3 = k1_xboole_0 ),
    inference(clc,[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X27 @ X26 )
        = X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('65',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) )
      | ( ( k8_setfam_1 @ X27 @ k1_xboole_0 )
        = X27 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('66',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('67',plain,(
    ! [X27: $i] :
      ( ( k8_setfam_1 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['42','63','67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CvsNwuXC08
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.30/1.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.30/1.50  % Solved by: fo/fo7.sh
% 1.30/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.50  % done 1377 iterations in 1.041s
% 1.30/1.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.30/1.50  % SZS output start Refutation
% 1.30/1.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.30/1.50  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 1.30/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.30/1.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.50  thf(sk_C_3_type, type, sk_C_3: $i).
% 1.30/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.50  thf(sk_D_type, type, sk_D: $i).
% 1.30/1.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.30/1.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.30/1.50  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 1.30/1.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.30/1.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.30/1.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.30/1.50  thf(sk_B_type, type, sk_B: $i > $i).
% 1.30/1.50  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.30/1.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.30/1.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.30/1.50  thf(t58_setfam_1, conjecture,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.30/1.50       ( ( r2_hidden @ B @ A ) =>
% 1.30/1.50         ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 1.30/1.50           ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ))).
% 1.30/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.50    (~( ![A:$i,B:$i,C:$i]:
% 1.30/1.50        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.30/1.50          ( ( r2_hidden @ B @ A ) =>
% 1.30/1.50            ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 1.30/1.50              ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ) )),
% 1.30/1.50    inference('cnf.neg', [status(esa)], [t58_setfam_1])).
% 1.30/1.50  thf('0', plain,
% 1.30/1.50      ((~ (r2_hidden @ sk_B_1 @ sk_D)
% 1.30/1.50        | ~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('1', plain,
% 1.30/1.50      ((~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))
% 1.30/1.50         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 1.30/1.50      inference('split', [status(esa)], ['0'])).
% 1.30/1.50  thf('2', plain,
% 1.30/1.50      (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) | 
% 1.30/1.50       ~ ((r2_hidden @ sk_B_1 @ sk_D))),
% 1.30/1.50      inference('split', [status(esa)], ['0'])).
% 1.30/1.50  thf('3', plain,
% 1.30/1.50      (((r2_hidden @ sk_D @ sk_C_3)
% 1.30/1.50        | ~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('4', plain,
% 1.30/1.50      (((r2_hidden @ sk_D @ sk_C_3)) | 
% 1.30/1.50       ~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 1.30/1.50      inference('split', [status(esa)], ['3'])).
% 1.30/1.50  thf('5', plain,
% 1.30/1.50      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf(redefinition_k6_setfam_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.30/1.50       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 1.30/1.50  thf('6', plain,
% 1.30/1.50      (![X30 : $i, X31 : $i]:
% 1.30/1.50         (((k6_setfam_1 @ X31 @ X30) = (k1_setfam_1 @ X30))
% 1.30/1.50          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X31))))),
% 1.30/1.50      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 1.30/1.50  thf('7', plain, (((k6_setfam_1 @ sk_A @ sk_C_3) = (k1_setfam_1 @ sk_C_3))),
% 1.30/1.50      inference('sup-', [status(thm)], ['5', '6'])).
% 1.30/1.50  thf('8', plain,
% 1.30/1.50      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf(d10_setfam_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.30/1.50       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.30/1.50           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 1.30/1.50         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 1.30/1.50  thf('9', plain,
% 1.30/1.50      (![X26 : $i, X27 : $i]:
% 1.30/1.50         (((X26) = (k1_xboole_0))
% 1.30/1.50          | ((k8_setfam_1 @ X27 @ X26) = (k6_setfam_1 @ X27 @ X26))
% 1.30/1.50          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27))))),
% 1.30/1.50      inference('cnf', [status(esa)], [d10_setfam_1])).
% 1.30/1.50  thf('10', plain,
% 1.30/1.50      ((((k8_setfam_1 @ sk_A @ sk_C_3) = (k6_setfam_1 @ sk_A @ sk_C_3))
% 1.30/1.50        | ((sk_C_3) = (k1_xboole_0)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['8', '9'])).
% 1.30/1.50  thf('11', plain,
% 1.30/1.50      (![X39 : $i]:
% 1.30/1.50         (~ (r2_hidden @ X39 @ sk_C_3)
% 1.30/1.50          | (r2_hidden @ sk_B_1 @ X39)
% 1.30/1.50          | (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('12', plain,
% 1.30/1.50      (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))
% 1.30/1.50         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 1.30/1.50      inference('split', [status(esa)], ['11'])).
% 1.30/1.50  thf('13', plain,
% 1.30/1.50      ((((r2_hidden @ sk_B_1 @ (k6_setfam_1 @ sk_A @ sk_C_3))
% 1.30/1.50         | ((sk_C_3) = (k1_xboole_0))))
% 1.30/1.50         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['10', '12'])).
% 1.30/1.50  thf('14', plain,
% 1.30/1.50      ((((r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_3))
% 1.30/1.50         | ((sk_C_3) = (k1_xboole_0))))
% 1.30/1.50         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 1.30/1.50      inference('sup+', [status(thm)], ['7', '13'])).
% 1.30/1.50  thf('15', plain,
% 1.30/1.50      (((r2_hidden @ sk_D @ sk_C_3)) <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 1.30/1.50      inference('split', [status(esa)], ['3'])).
% 1.30/1.50  thf(t4_setfam_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 1.30/1.50  thf('16', plain,
% 1.30/1.50      (![X32 : $i, X33 : $i]:
% 1.30/1.50         ((r1_tarski @ (k1_setfam_1 @ X32) @ X33) | ~ (r2_hidden @ X33 @ X32))),
% 1.30/1.50      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.30/1.50  thf('17', plain,
% 1.30/1.50      (((r1_tarski @ (k1_setfam_1 @ sk_C_3) @ sk_D))
% 1.30/1.50         <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['15', '16'])).
% 1.30/1.50  thf(d3_tarski, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( r1_tarski @ A @ B ) <=>
% 1.30/1.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.30/1.50  thf('18', plain,
% 1.30/1.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.30/1.50         (~ (r2_hidden @ X3 @ X4)
% 1.30/1.50          | (r2_hidden @ X3 @ X5)
% 1.30/1.50          | ~ (r1_tarski @ X4 @ X5))),
% 1.30/1.50      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.50  thf('19', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((r2_hidden @ X0 @ sk_D)
% 1.30/1.50           | ~ (r2_hidden @ X0 @ (k1_setfam_1 @ sk_C_3))))
% 1.30/1.50         <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['17', '18'])).
% 1.30/1.50  thf('20', plain,
% 1.30/1.50      (((((sk_C_3) = (k1_xboole_0)) | (r2_hidden @ sk_B_1 @ sk_D)))
% 1.30/1.50         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) & 
% 1.30/1.50             ((r2_hidden @ sk_D @ sk_C_3)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['14', '19'])).
% 1.30/1.50  thf('21', plain,
% 1.30/1.50      ((~ (r2_hidden @ sk_B_1 @ sk_D)) <= (~ ((r2_hidden @ sk_B_1 @ sk_D)))),
% 1.30/1.50      inference('split', [status(esa)], ['0'])).
% 1.30/1.50  thf('22', plain,
% 1.30/1.50      ((((sk_C_3) = (k1_xboole_0)))
% 1.30/1.50         <= (~ ((r2_hidden @ sk_B_1 @ sk_D)) & 
% 1.30/1.50             ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) & 
% 1.30/1.50             ((r2_hidden @ sk_D @ sk_C_3)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['20', '21'])).
% 1.30/1.50  thf('23', plain,
% 1.30/1.50      (((r2_hidden @ sk_D @ sk_C_3)) <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 1.30/1.50      inference('split', [status(esa)], ['3'])).
% 1.30/1.50  thf(d1_xboole_0, axiom,
% 1.30/1.50    (![A:$i]:
% 1.30/1.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.30/1.50  thf('24', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.30/1.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.30/1.50  thf('25', plain,
% 1.30/1.50      ((~ (v1_xboole_0 @ sk_C_3)) <= (((r2_hidden @ sk_D @ sk_C_3)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['23', '24'])).
% 1.30/1.50  thf('26', plain,
% 1.30/1.50      ((~ (v1_xboole_0 @ k1_xboole_0))
% 1.30/1.50         <= (~ ((r2_hidden @ sk_B_1 @ sk_D)) & 
% 1.30/1.50             ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) & 
% 1.30/1.50             ((r2_hidden @ sk_D @ sk_C_3)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['22', '25'])).
% 1.30/1.50  thf('27', plain,
% 1.30/1.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.30/1.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.30/1.50  thf('28', plain,
% 1.30/1.50      (![X4 : $i, X6 : $i]:
% 1.30/1.50         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.30/1.50      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.50  thf('29', plain,
% 1.30/1.50      (![X4 : $i, X6 : $i]:
% 1.30/1.50         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.30/1.50      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.50  thf('30', plain,
% 1.30/1.50      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['28', '29'])).
% 1.30/1.50  thf('31', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.30/1.50      inference('simplify', [status(thm)], ['30'])).
% 1.30/1.50  thf(t37_zfmisc_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.30/1.50  thf('32', plain,
% 1.30/1.50      (![X15 : $i, X16 : $i]:
% 1.30/1.50         ((r2_hidden @ X15 @ X16) | ~ (r1_tarski @ (k1_tarski @ X15) @ X16))),
% 1.30/1.50      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 1.30/1.50  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['31', '32'])).
% 1.30/1.50  thf(l35_zfmisc_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.30/1.50       ( r2_hidden @ A @ B ) ))).
% 1.30/1.50  thf('34', plain,
% 1.30/1.50      (![X12 : $i, X14 : $i]:
% 1.30/1.50         (((k4_xboole_0 @ (k1_tarski @ X12) @ X14) = (k1_xboole_0))
% 1.30/1.50          | ~ (r2_hidden @ X12 @ X14))),
% 1.30/1.50      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 1.30/1.50  thf('35', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.50  thf(t64_zfmisc_1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.30/1.50       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.30/1.50  thf('36', plain,
% 1.30/1.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.30/1.50         (((X18) != (X20))
% 1.30/1.50          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20))))),
% 1.30/1.50      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.30/1.50  thf('37', plain,
% 1.30/1.50      (![X19 : $i, X20 : $i]:
% 1.30/1.50         ~ (r2_hidden @ X20 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20)))),
% 1.30/1.50      inference('simplify', [status(thm)], ['36'])).
% 1.30/1.50  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.30/1.50      inference('sup-', [status(thm)], ['35', '37'])).
% 1.30/1.50  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.30/1.50      inference('sup-', [status(thm)], ['27', '38'])).
% 1.30/1.50  thf('40', plain,
% 1.30/1.50      (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))) | 
% 1.30/1.50       ~ ((r2_hidden @ sk_D @ sk_C_3)) | ((r2_hidden @ sk_B_1 @ sk_D))),
% 1.30/1.50      inference('demod', [status(thm)], ['26', '39'])).
% 1.30/1.50  thf('41', plain, (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 1.30/1.50      inference('sat_resolution*', [status(thm)], ['2', '4', '40'])).
% 1.30/1.50  thf('42', plain, (~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))),
% 1.30/1.50      inference('simpl_trail', [status(thm)], ['1', '41'])).
% 1.30/1.50  thf(t6_setfam_1, axiom,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 1.30/1.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 1.30/1.50  thf('43', plain,
% 1.30/1.50      (![X37 : $i, X38 : $i]:
% 1.30/1.50         (((X37) = (k1_xboole_0))
% 1.30/1.50          | (r2_hidden @ (sk_C_2 @ X38 @ X37) @ X37)
% 1.30/1.50          | (r1_tarski @ X38 @ (k1_setfam_1 @ X37)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t6_setfam_1])).
% 1.30/1.50  thf('44', plain,
% 1.30/1.50      ((![X39 : $i]:
% 1.30/1.50          (~ (r2_hidden @ X39 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X39)))
% 1.30/1.50         <= ((![X39 : $i]:
% 1.30/1.50                (~ (r2_hidden @ X39 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X39))))),
% 1.30/1.50      inference('split', [status(esa)], ['11'])).
% 1.30/1.50  thf('45', plain,
% 1.30/1.50      ((![X0 : $i]:
% 1.30/1.50          ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_C_3))
% 1.30/1.50           | ((sk_C_3) = (k1_xboole_0))
% 1.30/1.50           | (r2_hidden @ sk_B_1 @ (sk_C_2 @ X0 @ sk_C_3))))
% 1.30/1.50         <= ((![X39 : $i]:
% 1.30/1.50                (~ (r2_hidden @ X39 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X39))))),
% 1.30/1.50      inference('sup-', [status(thm)], ['43', '44'])).
% 1.30/1.50  thf('46', plain,
% 1.30/1.50      ((![X39 : $i]:
% 1.30/1.50          (~ (r2_hidden @ X39 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X39))) | 
% 1.30/1.50       ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 1.30/1.50      inference('split', [status(esa)], ['11'])).
% 1.30/1.50  thf('47', plain,
% 1.30/1.50      ((![X39 : $i]:
% 1.30/1.50          (~ (r2_hidden @ X39 @ sk_C_3) | (r2_hidden @ sk_B_1 @ X39)))),
% 1.30/1.50      inference('sat_resolution*', [status(thm)], ['2', '4', '40', '46'])).
% 1.30/1.50  thf('48', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_C_3))
% 1.30/1.50          | ((sk_C_3) = (k1_xboole_0))
% 1.30/1.50          | (r2_hidden @ sk_B_1 @ (sk_C_2 @ X0 @ sk_C_3)))),
% 1.30/1.50      inference('simpl_trail', [status(thm)], ['45', '47'])).
% 1.30/1.50  thf('49', plain,
% 1.30/1.50      (![X15 : $i, X17 : $i]:
% 1.30/1.50         ((r1_tarski @ (k1_tarski @ X15) @ X17) | ~ (r2_hidden @ X15 @ X17))),
% 1.30/1.50      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 1.30/1.50  thf('50', plain,
% 1.30/1.50      (![X0 : $i]:
% 1.30/1.50         (((sk_C_3) = (k1_xboole_0))
% 1.30/1.50          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_C_3))
% 1.30/1.50          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (sk_C_2 @ X0 @ sk_C_3)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['48', '49'])).
% 1.30/1.50  thf('51', plain,
% 1.30/1.50      (![X37 : $i, X38 : $i]:
% 1.30/1.50         (((X37) = (k1_xboole_0))
% 1.30/1.50          | ~ (r1_tarski @ X38 @ (sk_C_2 @ X38 @ X37))
% 1.30/1.50          | (r1_tarski @ X38 @ (k1_setfam_1 @ X37)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t6_setfam_1])).
% 1.30/1.50  thf('52', plain,
% 1.30/1.50      (((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_setfam_1 @ sk_C_3))
% 1.30/1.50        | ((sk_C_3) = (k1_xboole_0))
% 1.30/1.50        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_setfam_1 @ sk_C_3))
% 1.30/1.50        | ((sk_C_3) = (k1_xboole_0)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['50', '51'])).
% 1.30/1.50  thf('53', plain,
% 1.30/1.50      ((((sk_C_3) = (k1_xboole_0))
% 1.30/1.50        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_setfam_1 @ sk_C_3)))),
% 1.30/1.50      inference('simplify', [status(thm)], ['52'])).
% 1.30/1.50  thf('54', plain,
% 1.30/1.50      (![X15 : $i, X16 : $i]:
% 1.30/1.50         ((r2_hidden @ X15 @ X16) | ~ (r1_tarski @ (k1_tarski @ X15) @ X16))),
% 1.30/1.50      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 1.30/1.50  thf('55', plain,
% 1.30/1.50      ((((sk_C_3) = (k1_xboole_0))
% 1.30/1.50        | (r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_3)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['53', '54'])).
% 1.30/1.50  thf('56', plain,
% 1.30/1.50      ((((k8_setfam_1 @ sk_A @ sk_C_3) = (k6_setfam_1 @ sk_A @ sk_C_3))
% 1.30/1.50        | ((sk_C_3) = (k1_xboole_0)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['8', '9'])).
% 1.30/1.50  thf('57', plain,
% 1.30/1.50      ((~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))
% 1.30/1.50         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 1.30/1.50      inference('split', [status(esa)], ['0'])).
% 1.30/1.50  thf('58', plain,
% 1.30/1.50      (((~ (r2_hidden @ sk_B_1 @ (k6_setfam_1 @ sk_A @ sk_C_3))
% 1.30/1.50         | ((sk_C_3) = (k1_xboole_0))))
% 1.30/1.50         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 1.30/1.50      inference('sup-', [status(thm)], ['56', '57'])).
% 1.30/1.50  thf('59', plain, (((k6_setfam_1 @ sk_A @ sk_C_3) = (k1_setfam_1 @ sk_C_3))),
% 1.30/1.50      inference('sup-', [status(thm)], ['5', '6'])).
% 1.30/1.50  thf('60', plain,
% 1.30/1.50      (((~ (r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_3))
% 1.30/1.50         | ((sk_C_3) = (k1_xboole_0))))
% 1.30/1.50         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3))))),
% 1.30/1.50      inference('demod', [status(thm)], ['58', '59'])).
% 1.30/1.50  thf('61', plain, (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_3)))),
% 1.30/1.50      inference('sat_resolution*', [status(thm)], ['2', '4', '40'])).
% 1.30/1.50  thf('62', plain,
% 1.30/1.50      ((~ (r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_3))
% 1.30/1.50        | ((sk_C_3) = (k1_xboole_0)))),
% 1.30/1.50      inference('simpl_trail', [status(thm)], ['60', '61'])).
% 1.30/1.50  thf('63', plain, (((sk_C_3) = (k1_xboole_0))),
% 1.30/1.50      inference('clc', [status(thm)], ['55', '62'])).
% 1.30/1.50  thf('64', plain,
% 1.30/1.50      (![X26 : $i, X27 : $i]:
% 1.30/1.50         (((X26) != (k1_xboole_0))
% 1.30/1.50          | ((k8_setfam_1 @ X27 @ X26) = (X27))
% 1.30/1.50          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27))))),
% 1.30/1.50      inference('cnf', [status(esa)], [d10_setfam_1])).
% 1.30/1.50  thf('65', plain,
% 1.30/1.50      (![X27 : $i]:
% 1.30/1.50         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27)))
% 1.30/1.50          | ((k8_setfam_1 @ X27 @ k1_xboole_0) = (X27)))),
% 1.30/1.50      inference('simplify', [status(thm)], ['64'])).
% 1.30/1.50  thf(t4_subset_1, axiom,
% 1.30/1.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.30/1.50  thf('66', plain,
% 1.30/1.50      (![X25 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 1.30/1.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.30/1.50  thf('67', plain, (![X27 : $i]: ((k8_setfam_1 @ X27 @ k1_xboole_0) = (X27))),
% 1.30/1.50      inference('demod', [status(thm)], ['65', '66'])).
% 1.30/1.50  thf('68', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('69', plain, ($false),
% 1.30/1.50      inference('demod', [status(thm)], ['42', '63', '67', '68'])).
% 1.30/1.50  
% 1.30/1.50  % SZS output end Refutation
% 1.30/1.50  
% 1.30/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
