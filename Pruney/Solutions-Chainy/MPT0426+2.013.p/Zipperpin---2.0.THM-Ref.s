%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ctuDkXA8w

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:20 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 156 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  834 (1605 expanded)
%              Number of equality atoms :   36 (  49 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

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
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_D @ sk_C_4 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_D @ sk_C_4 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X27 @ ( k3_subset_1 @ X26 @ X25 ) )
      | ( r1_xboole_0 @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('15',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k6_setfam_1 @ X32 @ X31 )
        = ( k1_setfam_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('20',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_4 )
    = ( k1_setfam_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
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

thf('22',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X30 @ X29 )
        = ( k6_setfam_1 @ X30 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('23',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_4 )
      = ( k6_setfam_1 @ sk_A @ sk_C_4 ) )
    | ( sk_C_4 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_C_4 )
      | ( r2_hidden @ sk_B_1 @ X43 )
      | ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k6_setfam_1 @ sk_A @ sk_C_4 ) )
      | ( sk_C_4 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_4 ) )
      | ( sk_C_4 = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_D @ sk_C_4 )
   <= ( r2_hidden @ sk_D @ sk_C_4 ) ),
    inference(split,[status(esa)],['2'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('29',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('30',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C_4 ) @ sk_D )
   <= ( r2_hidden @ sk_D @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_D )
        | ~ ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_C_4 ) ) )
   <= ( r2_hidden @ sk_D @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( sk_C_4 = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ sk_D ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
      & ( r2_hidden @ sk_D @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( sk_C_4 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
      & ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
      & ( r2_hidden @ sk_D @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_D @ sk_C_4 )
   <= ( r2_hidden @ sk_D @ sk_C_4 ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,
    ( ( r2_hidden @ sk_D @ k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
      & ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
      & ( r2_hidden @ sk_D @ sk_C_4 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_D @ X0 )
   <= ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
      & ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
      & ( r2_hidden @ sk_D @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ~ ( r1_xboole_0 @ X1 @ X0 )
   <= ( ~ ( r2_hidden @ sk_B_1 @ sk_D )
      & ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
      & ( r2_hidden @ sk_D @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_C_4 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
    | ( r2_hidden @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['17','43'])).

thf('45',plain,
    ( ! [X43: $i] :
        ( ~ ( r2_hidden @ X43 @ sk_C_4 )
        | ( r2_hidden @ sk_B_1 @ X43 ) )
    | ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference(split,[status(esa)],['24'])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ X42 @ X41 ) @ X41 )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('47',plain,
    ( ! [X43: $i] :
        ( ~ ( r2_hidden @ X43 @ sk_C_4 )
        | ( r2_hidden @ sk_B_1 @ X43 ) )
   <= ! [X43: $i] :
        ( ~ ( r2_hidden @ X43 @ sk_C_4 )
        | ( r2_hidden @ sk_B_1 @ X43 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_C_4 ) )
        | ( sk_C_4 = k1_xboole_0 )
        | ( r2_hidden @ sk_B_1 @ ( sk_C_3 @ X0 @ sk_C_4 ) ) )
   <= ! [X43: $i] :
        ( ~ ( r2_hidden @ X43 @ sk_C_4 )
        | ( r2_hidden @ sk_B_1 @ X43 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('49',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( sk_C_4 = k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_C_4 ) )
        | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( sk_C_3 @ X0 @ sk_C_4 ) ) )
   <= ! [X43: $i] :
        ( ~ ( r2_hidden @ X43 @ sk_C_4 )
        | ( r2_hidden @ sk_B_1 @ X43 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( r1_tarski @ X42 @ ( sk_C_3 @ X42 @ X41 ) )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('52',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_setfam_1 @ sk_C_4 ) )
      | ( sk_C_4 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_setfam_1 @ sk_C_4 ) )
      | ( sk_C_4 = k1_xboole_0 ) )
   <= ! [X43: $i] :
        ( ~ ( r2_hidden @ X43 @ sk_C_4 )
        | ( r2_hidden @ sk_B_1 @ X43 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( sk_C_4 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_setfam_1 @ sk_C_4 ) ) )
   <= ! [X43: $i] :
        ( ~ ( r2_hidden @ X43 @ sk_C_4 )
        | ( r2_hidden @ sk_B_1 @ X43 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k1_tarski @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('55',plain,
    ( ( ( sk_C_4 = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_4 ) ) )
   <= ! [X43: $i] :
        ( ~ ( r2_hidden @ X43 @ sk_C_4 )
        | ( r2_hidden @ sk_B_1 @ X43 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C_4 )
    = ( k1_setfam_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('57',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C_4 )
      = ( k6_setfam_1 @ sk_A @ sk_C_4 ) )
    | ( sk_C_4 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( ~ ( r2_hidden @ sk_B_1 @ ( k6_setfam_1 @ sk_A @ sk_C_4 ) )
      | ( sk_C_4 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( r2_hidden @ sk_B_1 @ ( k1_setfam_1 @ sk_C_4 ) )
      | ( sk_C_4 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( ( sk_C_4 = k1_xboole_0 )
      | ( sk_C_4 = k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
      & ! [X43: $i] :
          ( ~ ( r2_hidden @ X43 @ sk_C_4 )
          | ( r2_hidden @ sk_B_1 @ X43 ) ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( sk_C_4 = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
      & ! [X43: $i] :
          ( ~ ( r2_hidden @ X43 @ sk_C_4 )
          | ( r2_hidden @ sk_B_1 @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
   <= ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) )
      & ! [X43: $i] :
          ( ~ ( r2_hidden @ X43 @ sk_C_4 )
          | ( r2_hidden @ sk_B_1 @ X43 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X30 @ X29 )
        = X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('66',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X30 ) ) )
      | ( ( k8_setfam_1 @ X30 @ k1_xboole_0 )
        = X30 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('68',plain,(
    ! [X30: $i] :
      ( ( k8_setfam_1 @ X30 @ k1_xboole_0 )
      = X30 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ! [X43: $i] :
          ( ~ ( r2_hidden @ X43 @ sk_C_4 )
          | ( r2_hidden @ sk_B_1 @ X43 ) )
    | ( r2_hidden @ sk_B_1 @ ( k8_setfam_1 @ sk_A @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['64','68','69'])).

thf('71',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','44','45','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ctuDkXA8w
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.00/1.17  % Solved by: fo/fo7.sh
% 1.00/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.17  % done 1653 iterations in 0.742s
% 1.00/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.00/1.17  % SZS output start Refutation
% 1.00/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.00/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.00/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.00/1.17  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.00/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.17  thf(sk_D_type, type, sk_D: $i).
% 1.00/1.17  thf(sk_C_4_type, type, sk_C_4: $i).
% 1.00/1.17  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 1.00/1.17  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 1.00/1.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.00/1.17  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.17  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.00/1.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.00/1.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.00/1.17  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.00/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.17  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 1.00/1.17  thf(t58_setfam_1, conjecture,
% 1.00/1.17    (![A:$i,B:$i,C:$i]:
% 1.00/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.00/1.17       ( ( r2_hidden @ B @ A ) =>
% 1.00/1.17         ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 1.00/1.17           ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ))).
% 1.00/1.17  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.17    (~( ![A:$i,B:$i,C:$i]:
% 1.00/1.17        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.00/1.17          ( ( r2_hidden @ B @ A ) =>
% 1.00/1.17            ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) ) <=>
% 1.00/1.17              ( ![D:$i]: ( ( r2_hidden @ D @ C ) => ( r2_hidden @ B @ D ) ) ) ) ) ) )),
% 1.00/1.17    inference('cnf.neg', [status(esa)], [t58_setfam_1])).
% 1.00/1.17  thf('0', plain,
% 1.00/1.17      ((~ (r2_hidden @ sk_B_1 @ sk_D)
% 1.00/1.17        | ~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))),
% 1.00/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.17  thf('1', plain,
% 1.00/1.17      (~ ((r2_hidden @ sk_B_1 @ sk_D)) | 
% 1.00/1.17       ~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))),
% 1.00/1.17      inference('split', [status(esa)], ['0'])).
% 1.00/1.17  thf('2', plain,
% 1.00/1.17      (((r2_hidden @ sk_D @ sk_C_4)
% 1.00/1.17        | ~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))),
% 1.00/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.17  thf('3', plain,
% 1.00/1.17      (((r2_hidden @ sk_D @ sk_C_4)) | 
% 1.00/1.17       ~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))),
% 1.00/1.17      inference('split', [status(esa)], ['2'])).
% 1.00/1.17  thf(t4_subset_1, axiom,
% 1.00/1.17    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.00/1.17  thf('4', plain,
% 1.00/1.17      (![X28 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 1.00/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.00/1.17  thf(d3_tarski, axiom,
% 1.00/1.17    (![A:$i,B:$i]:
% 1.00/1.17     ( ( r1_tarski @ A @ B ) <=>
% 1.00/1.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.00/1.17  thf('5', plain,
% 1.00/1.17      (![X4 : $i, X6 : $i]:
% 1.00/1.17         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.00/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.00/1.17  thf('6', plain,
% 1.00/1.17      (![X4 : $i, X6 : $i]:
% 1.00/1.17         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.00/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.00/1.17  thf('7', plain,
% 1.00/1.17      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.00/1.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.17  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.00/1.17      inference('simplify', [status(thm)], ['7'])).
% 1.00/1.17  thf(t3_subset, axiom,
% 1.00/1.17    (![A:$i,B:$i]:
% 1.00/1.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.00/1.17  thf('9', plain,
% 1.00/1.17      (![X33 : $i, X35 : $i]:
% 1.00/1.17         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 1.00/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 1.00/1.17  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.00/1.17      inference('sup-', [status(thm)], ['8', '9'])).
% 1.00/1.17  thf(t43_subset_1, axiom,
% 1.00/1.17    (![A:$i,B:$i]:
% 1.00/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.17       ( ![C:$i]:
% 1.00/1.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.17           ( ( r1_xboole_0 @ B @ C ) <=>
% 1.00/1.17             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.00/1.17  thf('11', plain,
% 1.00/1.17      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.00/1.17         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 1.00/1.17          | ~ (r1_tarski @ X27 @ (k3_subset_1 @ X26 @ X25))
% 1.00/1.17          | (r1_xboole_0 @ X27 @ X25)
% 1.00/1.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.00/1.17      inference('cnf', [status(esa)], [t43_subset_1])).
% 1.00/1.17  thf('12', plain,
% 1.00/1.17      (![X0 : $i, X1 : $i]:
% 1.00/1.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.00/1.17          | (r1_xboole_0 @ X1 @ X0)
% 1.00/1.17          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ X0)))),
% 1.00/1.17      inference('sup-', [status(thm)], ['10', '11'])).
% 1.00/1.17  thf('13', plain,
% 1.00/1.17      (![X0 : $i]:
% 1.00/1.17         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X0 @ X0))
% 1.00/1.17          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.00/1.17      inference('sup-', [status(thm)], ['4', '12'])).
% 1.00/1.17  thf('14', plain,
% 1.00/1.17      (![X28 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 1.00/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.00/1.17  thf('15', plain,
% 1.00/1.17      (![X33 : $i, X34 : $i]:
% 1.00/1.17         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 1.00/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 1.00/1.17  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.00/1.17      inference('sup-', [status(thm)], ['14', '15'])).
% 1.00/1.17  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.00/1.17      inference('demod', [status(thm)], ['13', '16'])).
% 1.00/1.17  thf('18', plain,
% 1.00/1.17      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.17  thf(redefinition_k6_setfam_1, axiom,
% 1.00/1.17    (![A:$i,B:$i]:
% 1.00/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.00/1.17       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 1.00/1.17  thf('19', plain,
% 1.00/1.17      (![X31 : $i, X32 : $i]:
% 1.00/1.17         (((k6_setfam_1 @ X32 @ X31) = (k1_setfam_1 @ X31))
% 1.00/1.17          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X32))))),
% 1.00/1.17      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 1.00/1.17  thf('20', plain, (((k6_setfam_1 @ sk_A @ sk_C_4) = (k1_setfam_1 @ sk_C_4))),
% 1.00/1.17      inference('sup-', [status(thm)], ['18', '19'])).
% 1.00/1.17  thf('21', plain,
% 1.00/1.17      ((m1_subset_1 @ sk_C_4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.17  thf(d10_setfam_1, axiom,
% 1.00/1.17    (![A:$i,B:$i]:
% 1.00/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.00/1.17       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.00/1.17           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 1.00/1.17         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 1.00/1.17  thf('22', plain,
% 1.00/1.17      (![X29 : $i, X30 : $i]:
% 1.00/1.17         (((X29) = (k1_xboole_0))
% 1.00/1.17          | ((k8_setfam_1 @ X30 @ X29) = (k6_setfam_1 @ X30 @ X29))
% 1.00/1.17          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X30))))),
% 1.00/1.17      inference('cnf', [status(esa)], [d10_setfam_1])).
% 1.00/1.17  thf('23', plain,
% 1.00/1.17      ((((k8_setfam_1 @ sk_A @ sk_C_4) = (k6_setfam_1 @ sk_A @ sk_C_4))
% 1.00/1.17        | ((sk_C_4) = (k1_xboole_0)))),
% 1.00/1.17      inference('sup-', [status(thm)], ['21', '22'])).
% 1.00/1.17  thf('24', plain,
% 1.00/1.17      (![X43 : $i]:
% 1.00/1.17         (~ (r2_hidden @ X43 @ sk_C_4)
% 1.00/1.17          | (r2_hidden @ sk_B_1 @ X43)
% 1.00/1.17          | (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))),
% 1.00/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.17  thf('25', plain,
% 1.00/1.17      (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))
% 1.00/1.17         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))))),
% 1.00/1.17      inference('split', [status(esa)], ['24'])).
% 1.00/1.17  thf('26', plain,
% 1.00/1.17      ((((r2_hidden @ sk_B_1 @ (k6_setfam_1 @ sk_A @ sk_C_4))
% 1.00/1.17         | ((sk_C_4) = (k1_xboole_0))))
% 1.00/1.17         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))))),
% 1.00/1.17      inference('sup+', [status(thm)], ['23', '25'])).
% 1.00/1.17  thf('27', plain,
% 1.00/1.17      ((((r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_4))
% 1.00/1.17         | ((sk_C_4) = (k1_xboole_0))))
% 1.00/1.17         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))))),
% 1.00/1.17      inference('sup+', [status(thm)], ['20', '26'])).
% 1.00/1.17  thf('28', plain,
% 1.00/1.17      (((r2_hidden @ sk_D @ sk_C_4)) <= (((r2_hidden @ sk_D @ sk_C_4)))),
% 1.00/1.17      inference('split', [status(esa)], ['2'])).
% 1.00/1.17  thf(t4_setfam_1, axiom,
% 1.00/1.17    (![A:$i,B:$i]:
% 1.00/1.17     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 1.00/1.17  thf('29', plain,
% 1.00/1.17      (![X36 : $i, X37 : $i]:
% 1.00/1.17         ((r1_tarski @ (k1_setfam_1 @ X36) @ X37) | ~ (r2_hidden @ X37 @ X36))),
% 1.00/1.17      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.00/1.17  thf('30', plain,
% 1.00/1.17      (((r1_tarski @ (k1_setfam_1 @ sk_C_4) @ sk_D))
% 1.00/1.17         <= (((r2_hidden @ sk_D @ sk_C_4)))),
% 1.00/1.17      inference('sup-', [status(thm)], ['28', '29'])).
% 1.00/1.17  thf('31', plain,
% 1.00/1.17      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.00/1.17         (~ (r2_hidden @ X3 @ X4)
% 1.00/1.17          | (r2_hidden @ X3 @ X5)
% 1.00/1.17          | ~ (r1_tarski @ X4 @ X5))),
% 1.00/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.00/1.17  thf('32', plain,
% 1.00/1.17      ((![X0 : $i]:
% 1.00/1.17          ((r2_hidden @ X0 @ sk_D)
% 1.00/1.17           | ~ (r2_hidden @ X0 @ (k1_setfam_1 @ sk_C_4))))
% 1.00/1.17         <= (((r2_hidden @ sk_D @ sk_C_4)))),
% 1.00/1.17      inference('sup-', [status(thm)], ['30', '31'])).
% 1.00/1.17  thf('33', plain,
% 1.00/1.17      (((((sk_C_4) = (k1_xboole_0)) | (r2_hidden @ sk_B_1 @ sk_D)))
% 1.00/1.17         <= (((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))) & 
% 1.00/1.17             ((r2_hidden @ sk_D @ sk_C_4)))),
% 1.00/1.17      inference('sup-', [status(thm)], ['27', '32'])).
% 1.00/1.17  thf('34', plain,
% 1.00/1.17      ((~ (r2_hidden @ sk_B_1 @ sk_D)) <= (~ ((r2_hidden @ sk_B_1 @ sk_D)))),
% 1.00/1.17      inference('split', [status(esa)], ['0'])).
% 1.00/1.17  thf('35', plain,
% 1.00/1.17      ((((sk_C_4) = (k1_xboole_0)))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ sk_D)) & 
% 1.00/1.17             ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))) & 
% 1.00/1.17             ((r2_hidden @ sk_D @ sk_C_4)))),
% 1.00/1.17      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.17  thf('36', plain,
% 1.00/1.17      (((r2_hidden @ sk_D @ sk_C_4)) <= (((r2_hidden @ sk_D @ sk_C_4)))),
% 1.00/1.17      inference('split', [status(esa)], ['2'])).
% 1.00/1.17  thf('37', plain,
% 1.00/1.17      (((r2_hidden @ sk_D @ k1_xboole_0))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ sk_D)) & 
% 1.00/1.17             ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))) & 
% 1.00/1.17             ((r2_hidden @ sk_D @ sk_C_4)))),
% 1.00/1.17      inference('sup+', [status(thm)], ['35', '36'])).
% 1.00/1.17  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.00/1.17      inference('sup-', [status(thm)], ['14', '15'])).
% 1.00/1.17  thf('39', plain,
% 1.00/1.17      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.00/1.17         (~ (r2_hidden @ X3 @ X4)
% 1.00/1.17          | (r2_hidden @ X3 @ X5)
% 1.00/1.17          | ~ (r1_tarski @ X4 @ X5))),
% 1.00/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.00/1.17  thf('40', plain,
% 1.00/1.17      (![X0 : $i, X1 : $i]:
% 1.00/1.17         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.00/1.17      inference('sup-', [status(thm)], ['38', '39'])).
% 1.00/1.17  thf('41', plain,
% 1.00/1.17      ((![X0 : $i]: (r2_hidden @ sk_D @ X0))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ sk_D)) & 
% 1.00/1.17             ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))) & 
% 1.00/1.17             ((r2_hidden @ sk_D @ sk_C_4)))),
% 1.00/1.17      inference('sup-', [status(thm)], ['37', '40'])).
% 1.00/1.17  thf(t4_xboole_0, axiom,
% 1.00/1.17    (![A:$i,B:$i]:
% 1.00/1.17     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.17            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.17       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.00/1.17            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.00/1.17  thf('42', plain,
% 1.00/1.17      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.00/1.17         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 1.00/1.17          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.00/1.17      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.17  thf('43', plain,
% 1.00/1.17      ((![X0 : $i, X1 : $i]: ~ (r1_xboole_0 @ X1 @ X0))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ sk_D)) & 
% 1.00/1.17             ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))) & 
% 1.00/1.17             ((r2_hidden @ sk_D @ sk_C_4)))),
% 1.00/1.17      inference('sup-', [status(thm)], ['41', '42'])).
% 1.00/1.17  thf('44', plain,
% 1.00/1.17      (~ ((r2_hidden @ sk_D @ sk_C_4)) | 
% 1.00/1.17       ~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))) | 
% 1.00/1.17       ((r2_hidden @ sk_B_1 @ sk_D))),
% 1.00/1.17      inference('sup-', [status(thm)], ['17', '43'])).
% 1.00/1.17  thf('45', plain,
% 1.00/1.17      ((![X43 : $i]:
% 1.00/1.17          (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))) | 
% 1.00/1.17       ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))),
% 1.00/1.17      inference('split', [status(esa)], ['24'])).
% 1.00/1.17  thf(t6_setfam_1, axiom,
% 1.00/1.17    (![A:$i,B:$i]:
% 1.00/1.17     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 1.00/1.17       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 1.00/1.17  thf('46', plain,
% 1.00/1.17      (![X41 : $i, X42 : $i]:
% 1.00/1.17         (((X41) = (k1_xboole_0))
% 1.00/1.17          | (r2_hidden @ (sk_C_3 @ X42 @ X41) @ X41)
% 1.00/1.17          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 1.00/1.17      inference('cnf', [status(esa)], [t6_setfam_1])).
% 1.00/1.17  thf('47', plain,
% 1.00/1.17      ((![X43 : $i]:
% 1.00/1.17          (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43)))
% 1.00/1.17         <= ((![X43 : $i]:
% 1.00/1.17                (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))))),
% 1.00/1.17      inference('split', [status(esa)], ['24'])).
% 1.00/1.17  thf('48', plain,
% 1.00/1.17      ((![X0 : $i]:
% 1.00/1.17          ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_C_4))
% 1.00/1.17           | ((sk_C_4) = (k1_xboole_0))
% 1.00/1.17           | (r2_hidden @ sk_B_1 @ (sk_C_3 @ X0 @ sk_C_4))))
% 1.00/1.17         <= ((![X43 : $i]:
% 1.00/1.17                (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))))),
% 1.00/1.17      inference('sup-', [status(thm)], ['46', '47'])).
% 1.00/1.17  thf(l1_zfmisc_1, axiom,
% 1.00/1.17    (![A:$i,B:$i]:
% 1.00/1.17     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.00/1.17  thf('49', plain,
% 1.00/1.17      (![X13 : $i, X15 : $i]:
% 1.00/1.17         ((r1_tarski @ (k1_tarski @ X13) @ X15) | ~ (r2_hidden @ X13 @ X15))),
% 1.00/1.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.00/1.17  thf('50', plain,
% 1.00/1.17      ((![X0 : $i]:
% 1.00/1.17          (((sk_C_4) = (k1_xboole_0))
% 1.00/1.17           | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_C_4))
% 1.00/1.17           | (r1_tarski @ (k1_tarski @ sk_B_1) @ (sk_C_3 @ X0 @ sk_C_4))))
% 1.00/1.17         <= ((![X43 : $i]:
% 1.00/1.17                (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))))),
% 1.00/1.17      inference('sup-', [status(thm)], ['48', '49'])).
% 1.00/1.17  thf('51', plain,
% 1.00/1.17      (![X41 : $i, X42 : $i]:
% 1.00/1.17         (((X41) = (k1_xboole_0))
% 1.00/1.17          | ~ (r1_tarski @ X42 @ (sk_C_3 @ X42 @ X41))
% 1.00/1.17          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 1.00/1.17      inference('cnf', [status(esa)], [t6_setfam_1])).
% 1.00/1.17  thf('52', plain,
% 1.00/1.17      ((((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_setfam_1 @ sk_C_4))
% 1.00/1.17         | ((sk_C_4) = (k1_xboole_0))
% 1.00/1.17         | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_setfam_1 @ sk_C_4))
% 1.00/1.17         | ((sk_C_4) = (k1_xboole_0))))
% 1.00/1.17         <= ((![X43 : $i]:
% 1.00/1.17                (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))))),
% 1.00/1.17      inference('sup-', [status(thm)], ['50', '51'])).
% 1.00/1.17  thf('53', plain,
% 1.00/1.17      (((((sk_C_4) = (k1_xboole_0))
% 1.00/1.17         | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_setfam_1 @ sk_C_4))))
% 1.00/1.17         <= ((![X43 : $i]:
% 1.00/1.17                (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))))),
% 1.00/1.17      inference('simplify', [status(thm)], ['52'])).
% 1.00/1.17  thf('54', plain,
% 1.00/1.17      (![X13 : $i, X14 : $i]:
% 1.00/1.17         ((r2_hidden @ X13 @ X14) | ~ (r1_tarski @ (k1_tarski @ X13) @ X14))),
% 1.00/1.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.00/1.17  thf('55', plain,
% 1.00/1.17      (((((sk_C_4) = (k1_xboole_0))
% 1.00/1.17         | (r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_4))))
% 1.00/1.17         <= ((![X43 : $i]:
% 1.00/1.17                (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))))),
% 1.00/1.17      inference('sup-', [status(thm)], ['53', '54'])).
% 1.00/1.17  thf('56', plain, (((k6_setfam_1 @ sk_A @ sk_C_4) = (k1_setfam_1 @ sk_C_4))),
% 1.00/1.17      inference('sup-', [status(thm)], ['18', '19'])).
% 1.00/1.17  thf('57', plain,
% 1.00/1.17      ((((k8_setfam_1 @ sk_A @ sk_C_4) = (k6_setfam_1 @ sk_A @ sk_C_4))
% 1.00/1.17        | ((sk_C_4) = (k1_xboole_0)))),
% 1.00/1.17      inference('sup-', [status(thm)], ['21', '22'])).
% 1.00/1.17  thf('58', plain,
% 1.00/1.17      ((~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))))),
% 1.00/1.17      inference('split', [status(esa)], ['0'])).
% 1.00/1.17  thf('59', plain,
% 1.00/1.17      (((~ (r2_hidden @ sk_B_1 @ (k6_setfam_1 @ sk_A @ sk_C_4))
% 1.00/1.17         | ((sk_C_4) = (k1_xboole_0))))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))))),
% 1.00/1.17      inference('sup-', [status(thm)], ['57', '58'])).
% 1.00/1.17  thf('60', plain,
% 1.00/1.17      (((~ (r2_hidden @ sk_B_1 @ (k1_setfam_1 @ sk_C_4))
% 1.00/1.17         | ((sk_C_4) = (k1_xboole_0))))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))))),
% 1.00/1.17      inference('sup-', [status(thm)], ['56', '59'])).
% 1.00/1.17  thf('61', plain,
% 1.00/1.17      (((((sk_C_4) = (k1_xboole_0)) | ((sk_C_4) = (k1_xboole_0))))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))) & 
% 1.00/1.17             (![X43 : $i]:
% 1.00/1.17                (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))))),
% 1.00/1.17      inference('sup-', [status(thm)], ['55', '60'])).
% 1.00/1.17  thf('62', plain,
% 1.00/1.17      ((((sk_C_4) = (k1_xboole_0)))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))) & 
% 1.00/1.17             (![X43 : $i]:
% 1.00/1.17                (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))))),
% 1.00/1.17      inference('simplify', [status(thm)], ['61'])).
% 1.00/1.17  thf('63', plain,
% 1.00/1.17      ((~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))))),
% 1.00/1.17      inference('split', [status(esa)], ['0'])).
% 1.00/1.17  thf('64', plain,
% 1.00/1.17      ((~ (r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ k1_xboole_0)))
% 1.00/1.17         <= (~ ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4))) & 
% 1.00/1.17             (![X43 : $i]:
% 1.00/1.17                (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))))),
% 1.00/1.17      inference('sup-', [status(thm)], ['62', '63'])).
% 1.00/1.17  thf('65', plain,
% 1.00/1.17      (![X29 : $i, X30 : $i]:
% 1.00/1.17         (((X29) != (k1_xboole_0))
% 1.00/1.17          | ((k8_setfam_1 @ X30 @ X29) = (X30))
% 1.00/1.17          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X30))))),
% 1.00/1.17      inference('cnf', [status(esa)], [d10_setfam_1])).
% 1.00/1.17  thf('66', plain,
% 1.00/1.17      (![X30 : $i]:
% 1.00/1.17         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X30)))
% 1.00/1.17          | ((k8_setfam_1 @ X30 @ k1_xboole_0) = (X30)))),
% 1.00/1.17      inference('simplify', [status(thm)], ['65'])).
% 1.00/1.17  thf('67', plain,
% 1.00/1.17      (![X28 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 1.00/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.00/1.17  thf('68', plain, (![X30 : $i]: ((k8_setfam_1 @ X30 @ k1_xboole_0) = (X30))),
% 1.00/1.17      inference('demod', [status(thm)], ['66', '67'])).
% 1.00/1.17  thf('69', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 1.00/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.17  thf('70', plain,
% 1.00/1.17      (~
% 1.00/1.17       (![X43 : $i]:
% 1.00/1.17          (~ (r2_hidden @ X43 @ sk_C_4) | (r2_hidden @ sk_B_1 @ X43))) | 
% 1.00/1.17       ((r2_hidden @ sk_B_1 @ (k8_setfam_1 @ sk_A @ sk_C_4)))),
% 1.00/1.17      inference('demod', [status(thm)], ['64', '68', '69'])).
% 1.00/1.17  thf('71', plain, ($false),
% 1.00/1.17      inference('sat_resolution*', [status(thm)], ['1', '3', '44', '45', '70'])).
% 1.00/1.17  
% 1.00/1.17  % SZS output end Refutation
% 1.00/1.17  
% 1.00/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
