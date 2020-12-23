%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LPSnZnXWIo

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:33 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 633 expanded)
%              Number of leaves         :   27 ( 185 expanded)
%              Depth                    :   14
%              Number of atoms          :  958 (9954 expanded)
%              Number of equality atoms :   32 ( 534 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(t12_compts_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( ( v2_compts_1 @ B @ A )
              <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) )
            & ( ( v2_pre_topc @ A )
             => ( ( B = k1_xboole_0 )
                | ( ( v2_compts_1 @ B @ A )
                <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( B = k1_xboole_0 )
               => ( ( v2_compts_1 @ B @ A )
                <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) )
              & ( ( v2_pre_topc @ A )
               => ( ( B = k1_xboole_0 )
                  | ( ( v2_compts_1 @ B @ A )
                  <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_compts_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k1_pre_topc @ X6 @ X5 ) )
      | ( ( k2_struct_0 @ X7 )
        = X5 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( v1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X6 @ X5 ) @ X6 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('6',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['3','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X8 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('13',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) )
               => ( ( v2_compts_1 @ C @ A )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( D = C )
                       => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X20 @ X18 ) @ X18 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_B @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_B @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('26',plain,
    ( ~ ( v2_compts_1 @ ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','24','25'])).

thf('27',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) )
        = X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( v2_compts_1 @ X20 @ X19 )
      | ( X21 != X20 )
      | ( v2_compts_1 @ X21 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v2_compts_1 @ X20 @ X18 )
      | ~ ( v2_compts_1 @ X20 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v2_compts_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v2_compts_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('46',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('47',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('49',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf('50',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('51',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','48','49','50'])).

thf('52',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf(t10_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_compts_1 @ A )
      <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) )).

thf('53',plain,(
    ! [X17: $i] :
      ( ~ ( v2_compts_1 @ ( k2_struct_0 @ X17 ) @ X17 )
      | ( v1_compts_1 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf('54',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,
    ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('63',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['29','63'])).

thf('65',plain,(
    ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','64'])).

thf('66',plain,(
    ~ ( v2_compts_1 @ ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['26','65'])).

thf('67',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ( ( sk_D @ X20 @ X18 )
        = X20 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ( ( sk_D @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_B @ sk_A )
      | ( ( sk_D @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('75',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('76',plain,
    ( ( ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','64'])).

thf('78',plain,
    ( ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['35'])).

thf('80',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf('81',plain,(
    ! [X17: $i] :
      ( ~ ( v1_compts_1 @ X17 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf('82',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('84',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('87',plain,(
    v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['29','63','86'])).

thf('88',plain,(
    v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['85','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['66','78','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LPSnZnXWIo
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:16:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.44/3.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.44/3.64  % Solved by: fo/fo7.sh
% 3.44/3.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.44/3.64  % done 1582 iterations in 3.167s
% 3.44/3.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.44/3.64  % SZS output start Refutation
% 3.44/3.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.44/3.64  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 3.44/3.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.44/3.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.44/3.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.44/3.64  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 3.44/3.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.44/3.64  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 3.44/3.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.44/3.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.44/3.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.44/3.64  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.44/3.64  thf(sk_B_type, type, sk_B: $i).
% 3.44/3.64  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.44/3.64  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 3.44/3.64  thf(sk_A_type, type, sk_A: $i).
% 3.44/3.64  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 3.44/3.64  thf(t12_compts_1, conjecture,
% 3.44/3.64    (![A:$i]:
% 3.44/3.64     ( ( l1_pre_topc @ A ) =>
% 3.44/3.64       ( ![B:$i]:
% 3.44/3.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.64           ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.44/3.64               ( ( v2_compts_1 @ B @ A ) <=>
% 3.44/3.64                 ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 3.44/3.64             ( ( v2_pre_topc @ A ) =>
% 3.44/3.64               ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.44/3.64                 ( ( v2_compts_1 @ B @ A ) <=>
% 3.44/3.64                   ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ))).
% 3.44/3.64  thf(zf_stmt_0, negated_conjecture,
% 3.44/3.64    (~( ![A:$i]:
% 3.44/3.64        ( ( l1_pre_topc @ A ) =>
% 3.44/3.64          ( ![B:$i]:
% 3.44/3.64            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.64              ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.44/3.64                  ( ( v2_compts_1 @ B @ A ) <=>
% 3.44/3.64                    ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 3.44/3.64                ( ( v2_pre_topc @ A ) =>
% 3.44/3.64                  ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.44/3.64                    ( ( v2_compts_1 @ B @ A ) <=>
% 3.44/3.64                      ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ) )),
% 3.44/3.64    inference('cnf.neg', [status(esa)], [t12_compts_1])).
% 3.44/3.64  thf('0', plain,
% 3.44/3.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf(d10_pre_topc, axiom,
% 3.44/3.64    (![A:$i]:
% 3.44/3.64     ( ( l1_pre_topc @ A ) =>
% 3.44/3.64       ( ![B:$i]:
% 3.44/3.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.64           ( ![C:$i]:
% 3.44/3.64             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.44/3.64               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 3.44/3.64                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 3.44/3.64  thf('1', plain,
% 3.44/3.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.44/3.64         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 3.44/3.64          | ((X7) != (k1_pre_topc @ X6 @ X5))
% 3.44/3.64          | ((k2_struct_0 @ X7) = (X5))
% 3.44/3.64          | ~ (m1_pre_topc @ X7 @ X6)
% 3.44/3.64          | ~ (v1_pre_topc @ X7)
% 3.44/3.64          | ~ (l1_pre_topc @ X6))),
% 3.44/3.64      inference('cnf', [status(esa)], [d10_pre_topc])).
% 3.44/3.64  thf('2', plain,
% 3.44/3.64      (![X5 : $i, X6 : $i]:
% 3.44/3.64         (~ (l1_pre_topc @ X6)
% 3.44/3.64          | ~ (v1_pre_topc @ (k1_pre_topc @ X6 @ X5))
% 3.44/3.64          | ~ (m1_pre_topc @ (k1_pre_topc @ X6 @ X5) @ X6)
% 3.44/3.64          | ((k2_struct_0 @ (k1_pre_topc @ X6 @ X5)) = (X5))
% 3.44/3.64          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 3.44/3.64      inference('simplify', [status(thm)], ['1'])).
% 3.44/3.64  thf('3', plain,
% 3.44/3.64      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 3.44/3.64        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 3.44/3.64        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.64        | ~ (l1_pre_topc @ sk_A))),
% 3.44/3.64      inference('sup-', [status(thm)], ['0', '2'])).
% 3.44/3.64  thf('4', plain,
% 3.44/3.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf(dt_k1_pre_topc, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( ( l1_pre_topc @ A ) & 
% 3.44/3.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.44/3.64       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 3.44/3.64         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 3.44/3.64  thf('5', plain,
% 3.44/3.64      (![X8 : $i, X9 : $i]:
% 3.44/3.64         (~ (l1_pre_topc @ X8)
% 3.44/3.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 3.44/3.64          | (v1_pre_topc @ (k1_pre_topc @ X8 @ X9)))),
% 3.44/3.64      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 3.44/3.64  thf('6', plain,
% 3.44/3.64      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)) | ~ (l1_pre_topc @ sk_A))),
% 3.44/3.64      inference('sup-', [status(thm)], ['4', '5'])).
% 3.44/3.64  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('8', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 3.44/3.64      inference('demod', [status(thm)], ['6', '7'])).
% 3.44/3.64  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('10', plain,
% 3.44/3.64      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 3.44/3.64        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 3.44/3.64      inference('demod', [status(thm)], ['3', '8', '9'])).
% 3.44/3.64  thf('11', plain,
% 3.44/3.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('12', plain,
% 3.44/3.64      (![X8 : $i, X9 : $i]:
% 3.44/3.64         (~ (l1_pre_topc @ X8)
% 3.44/3.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 3.44/3.64          | (m1_pre_topc @ (k1_pre_topc @ X8 @ X9) @ X8))),
% 3.44/3.64      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 3.44/3.64  thf('13', plain,
% 3.44/3.64      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 3.44/3.64        | ~ (l1_pre_topc @ sk_A))),
% 3.44/3.64      inference('sup-', [status(thm)], ['11', '12'])).
% 3.44/3.64  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('15', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 3.44/3.64      inference('demod', [status(thm)], ['13', '14'])).
% 3.44/3.64  thf('16', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 3.44/3.64      inference('demod', [status(thm)], ['10', '15'])).
% 3.44/3.64  thf('17', plain,
% 3.44/3.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf(t11_compts_1, axiom,
% 3.44/3.64    (![A:$i]:
% 3.44/3.64     ( ( l1_pre_topc @ A ) =>
% 3.44/3.64       ( ![B:$i]:
% 3.44/3.64         ( ( m1_pre_topc @ B @ A ) =>
% 3.44/3.64           ( ![C:$i]:
% 3.44/3.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.64               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 3.44/3.64                 ( ( v2_compts_1 @ C @ A ) <=>
% 3.44/3.64                   ( ![D:$i]:
% 3.44/3.64                     ( ( m1_subset_1 @
% 3.44/3.64                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 3.44/3.64                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 3.44/3.64  thf('18', plain,
% 3.44/3.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.44/3.64         (~ (m1_pre_topc @ X18 @ X19)
% 3.44/3.64          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 3.44/3.64          | ~ (v2_compts_1 @ (sk_D @ X20 @ X18) @ X18)
% 3.44/3.64          | (v2_compts_1 @ X20 @ X19)
% 3.44/3.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 3.44/3.64          | ~ (l1_pre_topc @ X19))),
% 3.44/3.64      inference('cnf', [status(esa)], [t11_compts_1])).
% 3.44/3.64  thf('19', plain,
% 3.44/3.64      (![X0 : $i]:
% 3.44/3.64         (~ (l1_pre_topc @ sk_A)
% 3.44/3.64          | (v2_compts_1 @ sk_B @ sk_A)
% 3.44/3.64          | ~ (v2_compts_1 @ (sk_D @ sk_B @ X0) @ X0)
% 3.44/3.64          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 3.44/3.64          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 3.44/3.64      inference('sup-', [status(thm)], ['17', '18'])).
% 3.44/3.64  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('21', plain,
% 3.44/3.64      (![X0 : $i]:
% 3.44/3.64         ((v2_compts_1 @ sk_B @ sk_A)
% 3.44/3.64          | ~ (v2_compts_1 @ (sk_D @ sk_B @ X0) @ X0)
% 3.44/3.64          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 3.44/3.64          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 3.44/3.64      inference('demod', [status(thm)], ['19', '20'])).
% 3.44/3.64  thf('22', plain,
% 3.44/3.64      ((~ (r1_tarski @ sk_B @ sk_B)
% 3.44/3.64        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 3.44/3.64        | ~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 3.44/3.64             (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.64        | (v2_compts_1 @ sk_B @ sk_A))),
% 3.44/3.64      inference('sup-', [status(thm)], ['16', '21'])).
% 3.44/3.64  thf(d10_xboole_0, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.44/3.64  thf('23', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.44/3.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.44/3.64  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.44/3.64      inference('simplify', [status(thm)], ['23'])).
% 3.44/3.64  thf('25', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 3.44/3.64      inference('demod', [status(thm)], ['13', '14'])).
% 3.44/3.64  thf('26', plain,
% 3.44/3.64      ((~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 3.44/3.64           (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.64        | (v2_compts_1 @ sk_B @ sk_A))),
% 3.44/3.64      inference('demod', [status(thm)], ['22', '24', '25'])).
% 3.44/3.64  thf('27', plain,
% 3.44/3.64      ((~ (v2_compts_1 @ sk_B @ sk_A)
% 3.44/3.64        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.64        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.64        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('28', plain,
% 3.44/3.64      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 3.44/3.64      inference('split', [status(esa)], ['27'])).
% 3.44/3.64  thf('29', plain,
% 3.44/3.64      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 3.44/3.64       ~ ((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 3.44/3.64      inference('split', [status(esa)], ['27'])).
% 3.44/3.64  thf('30', plain,
% 3.44/3.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf(t29_pre_topc, axiom,
% 3.44/3.64    (![A:$i]:
% 3.44/3.64     ( ( l1_pre_topc @ A ) =>
% 3.44/3.64       ( ![B:$i]:
% 3.44/3.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.44/3.64           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 3.44/3.64  thf('31', plain,
% 3.44/3.64      (![X12 : $i, X13 : $i]:
% 3.44/3.64         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 3.44/3.64          | ((u1_struct_0 @ (k1_pre_topc @ X13 @ X12)) = (X12))
% 3.44/3.64          | ~ (l1_pre_topc @ X13))),
% 3.44/3.64      inference('cnf', [status(esa)], [t29_pre_topc])).
% 3.44/3.64  thf('32', plain,
% 3.44/3.64      ((~ (l1_pre_topc @ sk_A)
% 3.44/3.64        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 3.44/3.64      inference('sup-', [status(thm)], ['30', '31'])).
% 3.44/3.64  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('34', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 3.44/3.64      inference('demod', [status(thm)], ['32', '33'])).
% 3.44/3.64  thf('35', plain,
% 3.44/3.64      (((v2_compts_1 @ sk_B @ sk_A)
% 3.44/3.64        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.64        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.64        | (v2_compts_1 @ sk_B @ sk_A))),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('36', plain,
% 3.44/3.64      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 3.44/3.64      inference('split', [status(esa)], ['35'])).
% 3.44/3.64  thf('37', plain,
% 3.44/3.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('38', plain,
% 3.44/3.64      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 3.44/3.64         (~ (m1_pre_topc @ X18 @ X19)
% 3.44/3.64          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 3.44/3.64          | ~ (v2_compts_1 @ X20 @ X19)
% 3.44/3.64          | ((X21) != (X20))
% 3.44/3.64          | (v2_compts_1 @ X21 @ X18)
% 3.44/3.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.44/3.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 3.44/3.64          | ~ (l1_pre_topc @ X19))),
% 3.44/3.64      inference('cnf', [status(esa)], [t11_compts_1])).
% 3.44/3.64  thf('39', plain,
% 3.44/3.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.44/3.65         (~ (l1_pre_topc @ X19)
% 3.44/3.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 3.44/3.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.44/3.65          | (v2_compts_1 @ X20 @ X18)
% 3.44/3.65          | ~ (v2_compts_1 @ X20 @ X19)
% 3.44/3.65          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 3.44/3.65          | ~ (m1_pre_topc @ X18 @ X19))),
% 3.44/3.65      inference('simplify', [status(thm)], ['38'])).
% 3.44/3.65  thf('40', plain,
% 3.44/3.65      (![X0 : $i]:
% 3.44/3.65         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.44/3.65          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 3.44/3.65          | ~ (v2_compts_1 @ sk_B @ sk_A)
% 3.44/3.65          | (v2_compts_1 @ sk_B @ X0)
% 3.44/3.65          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.44/3.65          | ~ (l1_pre_topc @ sk_A))),
% 3.44/3.65      inference('sup-', [status(thm)], ['37', '39'])).
% 3.44/3.65  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('42', plain,
% 3.44/3.65      (![X0 : $i]:
% 3.44/3.65         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.44/3.65          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 3.44/3.65          | ~ (v2_compts_1 @ sk_B @ sk_A)
% 3.44/3.65          | (v2_compts_1 @ sk_B @ X0)
% 3.44/3.65          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 3.44/3.65      inference('demod', [status(thm)], ['40', '41'])).
% 3.44/3.65  thf('43', plain,
% 3.44/3.65      ((![X0 : $i]:
% 3.44/3.65          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.44/3.65           | (v2_compts_1 @ sk_B @ X0)
% 3.44/3.65           | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 3.44/3.65           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 3.44/3.65         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['36', '42'])).
% 3.44/3.65  thf('44', plain,
% 3.44/3.65      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 3.44/3.65         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 3.44/3.65         | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 3.44/3.65         | (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))))
% 3.44/3.65         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['34', '43'])).
% 3.44/3.65  thf(dt_k2_subset_1, axiom,
% 3.44/3.65    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.44/3.65  thf('45', plain,
% 3.44/3.65      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 3.44/3.65      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 3.44/3.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.44/3.65  thf('46', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 3.44/3.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.44/3.65  thf('47', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 3.44/3.65      inference('demod', [status(thm)], ['45', '46'])).
% 3.44/3.65  thf('48', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 3.44/3.65      inference('demod', [status(thm)], ['13', '14'])).
% 3.44/3.65  thf('49', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 3.44/3.65      inference('demod', [status(thm)], ['10', '15'])).
% 3.44/3.65  thf('50', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.44/3.65      inference('simplify', [status(thm)], ['23'])).
% 3.44/3.65  thf('51', plain,
% 3.44/3.65      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)))
% 3.44/3.65         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 3.44/3.65      inference('demod', [status(thm)], ['44', '47', '48', '49', '50'])).
% 3.44/3.65  thf('52', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 3.44/3.65      inference('demod', [status(thm)], ['10', '15'])).
% 3.44/3.65  thf(t10_compts_1, axiom,
% 3.44/3.65    (![A:$i]:
% 3.44/3.65     ( ( l1_pre_topc @ A ) =>
% 3.44/3.65       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 3.44/3.65  thf('53', plain,
% 3.44/3.65      (![X17 : $i]:
% 3.44/3.65         (~ (v2_compts_1 @ (k2_struct_0 @ X17) @ X17)
% 3.44/3.65          | (v1_compts_1 @ X17)
% 3.44/3.65          | ~ (l1_pre_topc @ X17))),
% 3.44/3.65      inference('cnf', [status(esa)], [t10_compts_1])).
% 3.44/3.65  thf('54', plain,
% 3.44/3.65      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.65        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.65        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['52', '53'])).
% 3.44/3.65  thf('55', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 3.44/3.65      inference('demod', [status(thm)], ['13', '14'])).
% 3.44/3.65  thf(dt_m1_pre_topc, axiom,
% 3.44/3.65    (![A:$i]:
% 3.44/3.65     ( ( l1_pre_topc @ A ) =>
% 3.44/3.65       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 3.44/3.65  thf('56', plain,
% 3.44/3.65      (![X10 : $i, X11 : $i]:
% 3.44/3.65         (~ (m1_pre_topc @ X10 @ X11)
% 3.44/3.65          | (l1_pre_topc @ X10)
% 3.44/3.65          | ~ (l1_pre_topc @ X11))),
% 3.44/3.65      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 3.44/3.65  thf('57', plain,
% 3.44/3.65      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['55', '56'])).
% 3.44/3.65  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('59', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 3.44/3.65      inference('demod', [status(thm)], ['57', '58'])).
% 3.44/3.65  thf('60', plain,
% 3.44/3.65      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.65        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 3.44/3.65      inference('demod', [status(thm)], ['54', '59'])).
% 3.44/3.65  thf('61', plain,
% 3.44/3.65      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 3.44/3.65         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 3.44/3.65      inference('sup-', [status(thm)], ['51', '60'])).
% 3.44/3.65  thf('62', plain,
% 3.44/3.65      ((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 3.44/3.65         <= (~ ((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 3.44/3.65      inference('split', [status(esa)], ['27'])).
% 3.44/3.65  thf('63', plain,
% 3.44/3.65      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))) | 
% 3.44/3.65       ~ ((v2_compts_1 @ sk_B @ sk_A))),
% 3.44/3.65      inference('sup-', [status(thm)], ['61', '62'])).
% 3.44/3.65  thf('64', plain, (~ ((v2_compts_1 @ sk_B @ sk_A))),
% 3.44/3.65      inference('sat_resolution*', [status(thm)], ['29', '63'])).
% 3.44/3.65  thf('65', plain, (~ (v2_compts_1 @ sk_B @ sk_A)),
% 3.44/3.65      inference('simpl_trail', [status(thm)], ['28', '64'])).
% 3.44/3.65  thf('66', plain,
% 3.44/3.65      (~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 3.44/3.65          (k1_pre_topc @ sk_A @ sk_B))),
% 3.44/3.65      inference('clc', [status(thm)], ['26', '65'])).
% 3.44/3.65  thf('67', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 3.44/3.65      inference('demod', [status(thm)], ['10', '15'])).
% 3.44/3.65  thf('68', plain,
% 3.44/3.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('69', plain,
% 3.44/3.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.44/3.65         (~ (m1_pre_topc @ X18 @ X19)
% 3.44/3.65          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 3.44/3.65          | ((sk_D @ X20 @ X18) = (X20))
% 3.44/3.65          | (v2_compts_1 @ X20 @ X19)
% 3.44/3.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 3.44/3.65          | ~ (l1_pre_topc @ X19))),
% 3.44/3.65      inference('cnf', [status(esa)], [t11_compts_1])).
% 3.44/3.65  thf('70', plain,
% 3.44/3.65      (![X0 : $i]:
% 3.44/3.65         (~ (l1_pre_topc @ sk_A)
% 3.44/3.65          | (v2_compts_1 @ sk_B @ sk_A)
% 3.44/3.65          | ((sk_D @ sk_B @ X0) = (sk_B))
% 3.44/3.65          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 3.44/3.65          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 3.44/3.65      inference('sup-', [status(thm)], ['68', '69'])).
% 3.44/3.65  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 3.44/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.65  thf('72', plain,
% 3.44/3.65      (![X0 : $i]:
% 3.44/3.65         ((v2_compts_1 @ sk_B @ sk_A)
% 3.44/3.65          | ((sk_D @ sk_B @ X0) = (sk_B))
% 3.44/3.65          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 3.44/3.65          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 3.44/3.65      inference('demod', [status(thm)], ['70', '71'])).
% 3.44/3.65  thf('73', plain,
% 3.44/3.65      ((~ (r1_tarski @ sk_B @ sk_B)
% 3.44/3.65        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 3.44/3.65        | ((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 3.44/3.65        | (v2_compts_1 @ sk_B @ sk_A))),
% 3.44/3.65      inference('sup-', [status(thm)], ['67', '72'])).
% 3.44/3.65  thf('74', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.44/3.65      inference('simplify', [status(thm)], ['23'])).
% 3.44/3.65  thf('75', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 3.44/3.65      inference('demod', [status(thm)], ['13', '14'])).
% 3.44/3.65  thf('76', plain,
% 3.44/3.65      ((((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 3.44/3.65        | (v2_compts_1 @ sk_B @ sk_A))),
% 3.44/3.65      inference('demod', [status(thm)], ['73', '74', '75'])).
% 3.44/3.65  thf('77', plain, (~ (v2_compts_1 @ sk_B @ sk_A)),
% 3.44/3.65      inference('simpl_trail', [status(thm)], ['28', '64'])).
% 3.44/3.65  thf('78', plain, (((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 3.44/3.65      inference('clc', [status(thm)], ['76', '77'])).
% 3.44/3.65  thf('79', plain,
% 3.44/3.65      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 3.44/3.65         <= (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 3.44/3.65      inference('split', [status(esa)], ['35'])).
% 3.44/3.65  thf('80', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 3.44/3.65      inference('demod', [status(thm)], ['10', '15'])).
% 3.44/3.65  thf('81', plain,
% 3.44/3.65      (![X17 : $i]:
% 3.44/3.65         (~ (v1_compts_1 @ X17)
% 3.44/3.65          | (v2_compts_1 @ (k2_struct_0 @ X17) @ X17)
% 3.44/3.65          | ~ (l1_pre_topc @ X17))),
% 3.44/3.65      inference('cnf', [status(esa)], [t10_compts_1])).
% 3.44/3.65  thf('82', plain,
% 3.44/3.65      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.65        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.65        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 3.44/3.65      inference('sup+', [status(thm)], ['80', '81'])).
% 3.44/3.65  thf('83', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 3.44/3.65      inference('demod', [status(thm)], ['57', '58'])).
% 3.44/3.65  thf('84', plain,
% 3.44/3.65      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 3.44/3.65        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 3.44/3.65      inference('demod', [status(thm)], ['82', '83'])).
% 3.44/3.65  thf('85', plain,
% 3.44/3.65      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)))
% 3.44/3.65         <= (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 3.44/3.65      inference('sup-', [status(thm)], ['79', '84'])).
% 3.44/3.65  thf('86', plain,
% 3.44/3.65      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))) | 
% 3.44/3.65       ((v2_compts_1 @ sk_B @ sk_A))),
% 3.44/3.65      inference('split', [status(esa)], ['35'])).
% 3.44/3.65  thf('87', plain, (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 3.44/3.65      inference('sat_resolution*', [status(thm)], ['29', '63', '86'])).
% 3.44/3.65  thf('88', plain, ((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))),
% 3.44/3.65      inference('simpl_trail', [status(thm)], ['85', '87'])).
% 3.44/3.65  thf('89', plain, ($false),
% 3.44/3.65      inference('demod', [status(thm)], ['66', '78', '88'])).
% 3.44/3.65  
% 3.44/3.65  % SZS output end Refutation
% 3.44/3.65  
% 3.44/3.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
