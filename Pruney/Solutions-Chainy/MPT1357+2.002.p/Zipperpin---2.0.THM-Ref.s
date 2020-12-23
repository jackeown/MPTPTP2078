%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oUqgERejNC

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:34 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 635 expanded)
%              Number of leaves         :   25 ( 184 expanded)
%              Depth                    :   14
%              Number of atoms          :  957 (9996 expanded)
%              Number of equality atoms :   30 ( 534 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X8
       != ( k1_pre_topc @ X7 @ X6 ) )
      | ( ( k2_struct_0 @ X8 )
        = X6 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X9 @ X10 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X9 @ X10 ) @ X9 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ ( k2_struct_0 @ X19 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X21 @ X19 ) @ X19 )
      | ( v2_compts_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ ( k2_struct_0 @ X19 ) )
      | ~ ( v2_compts_1 @ X21 @ X20 )
      | ( X22 != X21 )
      | ( v2_compts_1 @ X22 @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_compts_1 @ X21 @ X19 )
      | ~ ( v2_compts_1 @ X21 @ X20 )
      | ~ ( r1_tarski @ X21 @ ( k2_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X19 @ X20 ) ) ),
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

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

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
    ! [X18: $i] :
      ( ~ ( v2_compts_1 @ ( k2_struct_0 @ X18 ) @ X18 )
      | ( v1_compts_1 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ ( k2_struct_0 @ X19 ) )
      | ( ( sk_D @ X21 @ X19 )
        = X21 )
      | ( v2_compts_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X18: $i] :
      ( ~ ( v1_compts_1 @ X18 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oUqgERejNC
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:17:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.25/2.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.25/2.46  % Solved by: fo/fo7.sh
% 2.25/2.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.25/2.46  % done 1145 iterations in 2.008s
% 2.25/2.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.25/2.46  % SZS output start Refutation
% 2.25/2.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.25/2.46  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 2.25/2.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.25/2.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.25/2.46  thf(sk_A_type, type, sk_A: $i).
% 2.25/2.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.25/2.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.25/2.46  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 2.25/2.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.25/2.46  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 2.25/2.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.25/2.46  thf(sk_B_type, type, sk_B: $i).
% 2.25/2.46  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.25/2.46  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.25/2.46  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 2.25/2.46  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 2.25/2.46  thf(t12_compts_1, conjecture,
% 2.25/2.46    (![A:$i]:
% 2.25/2.46     ( ( l1_pre_topc @ A ) =>
% 2.25/2.46       ( ![B:$i]:
% 2.25/2.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.25/2.46           ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.25/2.46               ( ( v2_compts_1 @ B @ A ) <=>
% 2.25/2.46                 ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 2.25/2.46             ( ( v2_pre_topc @ A ) =>
% 2.25/2.46               ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.25/2.46                 ( ( v2_compts_1 @ B @ A ) <=>
% 2.25/2.46                   ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ))).
% 2.25/2.46  thf(zf_stmt_0, negated_conjecture,
% 2.25/2.46    (~( ![A:$i]:
% 2.25/2.46        ( ( l1_pre_topc @ A ) =>
% 2.25/2.46          ( ![B:$i]:
% 2.25/2.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.25/2.46              ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.25/2.46                  ( ( v2_compts_1 @ B @ A ) <=>
% 2.25/2.46                    ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 2.25/2.46                ( ( v2_pre_topc @ A ) =>
% 2.25/2.46                  ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.25/2.46                    ( ( v2_compts_1 @ B @ A ) <=>
% 2.25/2.46                      ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ) )),
% 2.25/2.46    inference('cnf.neg', [status(esa)], [t12_compts_1])).
% 2.25/2.46  thf('0', plain,
% 2.25/2.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf(d10_pre_topc, axiom,
% 2.25/2.46    (![A:$i]:
% 2.25/2.46     ( ( l1_pre_topc @ A ) =>
% 2.25/2.46       ( ![B:$i]:
% 2.25/2.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.25/2.46           ( ![C:$i]:
% 2.25/2.46             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.25/2.46               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 2.25/2.46                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 2.25/2.46  thf('1', plain,
% 2.25/2.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.25/2.46         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 2.25/2.46          | ((X8) != (k1_pre_topc @ X7 @ X6))
% 2.25/2.46          | ((k2_struct_0 @ X8) = (X6))
% 2.25/2.46          | ~ (m1_pre_topc @ X8 @ X7)
% 2.25/2.46          | ~ (v1_pre_topc @ X8)
% 2.25/2.46          | ~ (l1_pre_topc @ X7))),
% 2.25/2.46      inference('cnf', [status(esa)], [d10_pre_topc])).
% 2.25/2.46  thf('2', plain,
% 2.25/2.46      (![X6 : $i, X7 : $i]:
% 2.25/2.46         (~ (l1_pre_topc @ X7)
% 2.25/2.46          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 2.25/2.46          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 2.25/2.46          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 2.25/2.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 2.25/2.46      inference('simplify', [status(thm)], ['1'])).
% 2.25/2.46  thf('3', plain,
% 2.25/2.46      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 2.25/2.46        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.25/2.46        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | ~ (l1_pre_topc @ sk_A))),
% 2.25/2.46      inference('sup-', [status(thm)], ['0', '2'])).
% 2.25/2.46  thf('4', plain,
% 2.25/2.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf(dt_k1_pre_topc, axiom,
% 2.25/2.46    (![A:$i,B:$i]:
% 2.25/2.46     ( ( ( l1_pre_topc @ A ) & 
% 2.25/2.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.25/2.46       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 2.25/2.46         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 2.25/2.46  thf('5', plain,
% 2.25/2.46      (![X9 : $i, X10 : $i]:
% 2.25/2.46         (~ (l1_pre_topc @ X9)
% 2.25/2.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 2.25/2.46          | (v1_pre_topc @ (k1_pre_topc @ X9 @ X10)))),
% 2.25/2.46      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 2.25/2.46  thf('6', plain,
% 2.25/2.46      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)) | ~ (l1_pre_topc @ sk_A))),
% 2.25/2.46      inference('sup-', [status(thm)], ['4', '5'])).
% 2.25/2.46  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('8', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.25/2.46      inference('demod', [status(thm)], ['6', '7'])).
% 2.25/2.46  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('10', plain,
% 2.25/2.46      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 2.25/2.46        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 2.25/2.46      inference('demod', [status(thm)], ['3', '8', '9'])).
% 2.25/2.46  thf('11', plain,
% 2.25/2.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('12', plain,
% 2.25/2.46      (![X9 : $i, X10 : $i]:
% 2.25/2.46         (~ (l1_pre_topc @ X9)
% 2.25/2.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 2.25/2.46          | (m1_pre_topc @ (k1_pre_topc @ X9 @ X10) @ X9))),
% 2.25/2.46      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 2.25/2.46  thf('13', plain,
% 2.25/2.46      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.25/2.46        | ~ (l1_pre_topc @ sk_A))),
% 2.25/2.46      inference('sup-', [status(thm)], ['11', '12'])).
% 2.25/2.46  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('15', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.25/2.46      inference('demod', [status(thm)], ['13', '14'])).
% 2.25/2.46  thf('16', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.25/2.46      inference('demod', [status(thm)], ['10', '15'])).
% 2.25/2.46  thf('17', plain,
% 2.25/2.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf(t11_compts_1, axiom,
% 2.25/2.46    (![A:$i]:
% 2.25/2.46     ( ( l1_pre_topc @ A ) =>
% 2.25/2.46       ( ![B:$i]:
% 2.25/2.46         ( ( m1_pre_topc @ B @ A ) =>
% 2.25/2.46           ( ![C:$i]:
% 2.25/2.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.25/2.46               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 2.25/2.46                 ( ( v2_compts_1 @ C @ A ) <=>
% 2.25/2.46                   ( ![D:$i]:
% 2.25/2.46                     ( ( m1_subset_1 @
% 2.25/2.46                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 2.25/2.46                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 2.25/2.46  thf('18', plain,
% 2.25/2.46      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.25/2.46         (~ (m1_pre_topc @ X19 @ X20)
% 2.25/2.46          | ~ (r1_tarski @ X21 @ (k2_struct_0 @ X19))
% 2.25/2.46          | ~ (v2_compts_1 @ (sk_D @ X21 @ X19) @ X19)
% 2.25/2.46          | (v2_compts_1 @ X21 @ X20)
% 2.25/2.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.25/2.46          | ~ (l1_pre_topc @ X20))),
% 2.25/2.46      inference('cnf', [status(esa)], [t11_compts_1])).
% 2.25/2.46  thf('19', plain,
% 2.25/2.46      (![X0 : $i]:
% 2.25/2.46         (~ (l1_pre_topc @ sk_A)
% 2.25/2.46          | (v2_compts_1 @ sk_B @ sk_A)
% 2.25/2.46          | ~ (v2_compts_1 @ (sk_D @ sk_B @ X0) @ X0)
% 2.25/2.46          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.25/2.46          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.25/2.46      inference('sup-', [status(thm)], ['17', '18'])).
% 2.25/2.46  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('21', plain,
% 2.25/2.46      (![X0 : $i]:
% 2.25/2.46         ((v2_compts_1 @ sk_B @ sk_A)
% 2.25/2.46          | ~ (v2_compts_1 @ (sk_D @ sk_B @ X0) @ X0)
% 2.25/2.46          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.25/2.46          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.25/2.46      inference('demod', [status(thm)], ['19', '20'])).
% 2.25/2.46  thf('22', plain,
% 2.25/2.46      ((~ (r1_tarski @ sk_B @ sk_B)
% 2.25/2.46        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.25/2.46        | ~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 2.25/2.46             (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.25/2.46      inference('sup-', [status(thm)], ['16', '21'])).
% 2.25/2.46  thf(d10_xboole_0, axiom,
% 2.25/2.46    (![A:$i,B:$i]:
% 2.25/2.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.25/2.46  thf('23', plain,
% 2.25/2.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.25/2.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.25/2.46  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.25/2.46      inference('simplify', [status(thm)], ['23'])).
% 2.25/2.46  thf('25', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.25/2.46      inference('demod', [status(thm)], ['13', '14'])).
% 2.25/2.46  thf('26', plain,
% 2.25/2.46      ((~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 2.25/2.46           (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.25/2.46      inference('demod', [status(thm)], ['22', '24', '25'])).
% 2.25/2.46  thf('27', plain,
% 2.25/2.46      ((~ (v2_compts_1 @ sk_B @ sk_A)
% 2.25/2.46        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('28', plain,
% 2.25/2.46      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 2.25/2.46      inference('split', [status(esa)], ['27'])).
% 2.25/2.46  thf('29', plain,
% 2.25/2.46      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 2.25/2.46       ~ ((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.25/2.46      inference('split', [status(esa)], ['27'])).
% 2.25/2.46  thf('30', plain,
% 2.25/2.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf(t29_pre_topc, axiom,
% 2.25/2.46    (![A:$i]:
% 2.25/2.46     ( ( l1_pre_topc @ A ) =>
% 2.25/2.46       ( ![B:$i]:
% 2.25/2.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.25/2.46           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 2.25/2.46  thf('31', plain,
% 2.25/2.46      (![X13 : $i, X14 : $i]:
% 2.25/2.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 2.25/2.46          | ((u1_struct_0 @ (k1_pre_topc @ X14 @ X13)) = (X13))
% 2.25/2.46          | ~ (l1_pre_topc @ X14))),
% 2.25/2.46      inference('cnf', [status(esa)], [t29_pre_topc])).
% 2.25/2.46  thf('32', plain,
% 2.25/2.46      ((~ (l1_pre_topc @ sk_A)
% 2.25/2.46        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 2.25/2.46      inference('sup-', [status(thm)], ['30', '31'])).
% 2.25/2.46  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('34', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.25/2.46      inference('demod', [status(thm)], ['32', '33'])).
% 2.25/2.46  thf('35', plain,
% 2.25/2.46      (((v2_compts_1 @ sk_B @ sk_A)
% 2.25/2.46        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('36', plain,
% 2.25/2.46      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.25/2.46      inference('split', [status(esa)], ['35'])).
% 2.25/2.46  thf('37', plain,
% 2.25/2.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('38', plain,
% 2.25/2.46      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 2.25/2.46         (~ (m1_pre_topc @ X19 @ X20)
% 2.25/2.46          | ~ (r1_tarski @ X21 @ (k2_struct_0 @ X19))
% 2.25/2.46          | ~ (v2_compts_1 @ X21 @ X20)
% 2.25/2.46          | ((X22) != (X21))
% 2.25/2.46          | (v2_compts_1 @ X22 @ X19)
% 2.25/2.46          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.25/2.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.25/2.46          | ~ (l1_pre_topc @ X20))),
% 2.25/2.46      inference('cnf', [status(esa)], [t11_compts_1])).
% 2.25/2.46  thf('39', plain,
% 2.25/2.46      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.25/2.46         (~ (l1_pre_topc @ X20)
% 2.25/2.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.25/2.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.25/2.46          | (v2_compts_1 @ X21 @ X19)
% 2.25/2.46          | ~ (v2_compts_1 @ X21 @ X20)
% 2.25/2.46          | ~ (r1_tarski @ X21 @ (k2_struct_0 @ X19))
% 2.25/2.46          | ~ (m1_pre_topc @ X19 @ X20))),
% 2.25/2.46      inference('simplify', [status(thm)], ['38'])).
% 2.25/2.46  thf('40', plain,
% 2.25/2.46      (![X0 : $i]:
% 2.25/2.46         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.25/2.46          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.25/2.46          | ~ (v2_compts_1 @ sk_B @ sk_A)
% 2.25/2.46          | (v2_compts_1 @ sk_B @ X0)
% 2.25/2.46          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.25/2.46          | ~ (l1_pre_topc @ sk_A))),
% 2.25/2.46      inference('sup-', [status(thm)], ['37', '39'])).
% 2.25/2.46  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('42', plain,
% 2.25/2.46      (![X0 : $i]:
% 2.25/2.46         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.25/2.46          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.25/2.46          | ~ (v2_compts_1 @ sk_B @ sk_A)
% 2.25/2.46          | (v2_compts_1 @ sk_B @ X0)
% 2.25/2.46          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 2.25/2.46      inference('demod', [status(thm)], ['40', '41'])).
% 2.25/2.46  thf('43', plain,
% 2.25/2.46      ((![X0 : $i]:
% 2.25/2.46          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.25/2.46           | (v2_compts_1 @ sk_B @ X0)
% 2.25/2.46           | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.25/2.46           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 2.25/2.46         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.25/2.46      inference('sup-', [status(thm)], ['36', '42'])).
% 2.25/2.46  thf('44', plain,
% 2.25/2.46      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 2.25/2.46         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.25/2.46         | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.25/2.46         | (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))))
% 2.25/2.46         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.25/2.46      inference('sup-', [status(thm)], ['34', '43'])).
% 2.25/2.46  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.25/2.46      inference('simplify', [status(thm)], ['23'])).
% 2.25/2.46  thf(t3_subset, axiom,
% 2.25/2.46    (![A:$i,B:$i]:
% 2.25/2.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.25/2.46  thf('46', plain,
% 2.25/2.46      (![X3 : $i, X5 : $i]:
% 2.25/2.46         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 2.25/2.46      inference('cnf', [status(esa)], [t3_subset])).
% 2.25/2.46  thf('47', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.25/2.46      inference('sup-', [status(thm)], ['45', '46'])).
% 2.25/2.46  thf('48', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.25/2.46      inference('demod', [status(thm)], ['13', '14'])).
% 2.25/2.46  thf('49', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.25/2.46      inference('demod', [status(thm)], ['10', '15'])).
% 2.25/2.46  thf('50', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.25/2.46      inference('simplify', [status(thm)], ['23'])).
% 2.25/2.46  thf('51', plain,
% 2.25/2.46      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.25/2.46         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.25/2.46      inference('demod', [status(thm)], ['44', '47', '48', '49', '50'])).
% 2.25/2.46  thf('52', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.25/2.46      inference('demod', [status(thm)], ['10', '15'])).
% 2.25/2.46  thf(t10_compts_1, axiom,
% 2.25/2.46    (![A:$i]:
% 2.25/2.46     ( ( l1_pre_topc @ A ) =>
% 2.25/2.46       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 2.25/2.46  thf('53', plain,
% 2.25/2.46      (![X18 : $i]:
% 2.25/2.46         (~ (v2_compts_1 @ (k2_struct_0 @ X18) @ X18)
% 2.25/2.46          | (v1_compts_1 @ X18)
% 2.25/2.46          | ~ (l1_pre_topc @ X18))),
% 2.25/2.46      inference('cnf', [status(esa)], [t10_compts_1])).
% 2.25/2.46  thf('54', plain,
% 2.25/2.46      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.25/2.46      inference('sup-', [status(thm)], ['52', '53'])).
% 2.25/2.46  thf('55', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.25/2.46      inference('demod', [status(thm)], ['13', '14'])).
% 2.25/2.46  thf(dt_m1_pre_topc, axiom,
% 2.25/2.46    (![A:$i]:
% 2.25/2.46     ( ( l1_pre_topc @ A ) =>
% 2.25/2.46       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 2.25/2.46  thf('56', plain,
% 2.25/2.46      (![X11 : $i, X12 : $i]:
% 2.25/2.46         (~ (m1_pre_topc @ X11 @ X12)
% 2.25/2.46          | (l1_pre_topc @ X11)
% 2.25/2.46          | ~ (l1_pre_topc @ X12))),
% 2.25/2.46      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 2.25/2.46  thf('57', plain,
% 2.25/2.46      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.25/2.46      inference('sup-', [status(thm)], ['55', '56'])).
% 2.25/2.46  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('59', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.25/2.46      inference('demod', [status(thm)], ['57', '58'])).
% 2.25/2.46  thf('60', plain,
% 2.25/2.46      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.25/2.46      inference('demod', [status(thm)], ['54', '59'])).
% 2.25/2.46  thf('61', plain,
% 2.25/2.46      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.25/2.46         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.25/2.46      inference('sup-', [status(thm)], ['51', '60'])).
% 2.25/2.46  thf('62', plain,
% 2.25/2.46      ((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.25/2.46         <= (~ ((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 2.25/2.46      inference('split', [status(esa)], ['27'])).
% 2.25/2.46  thf('63', plain,
% 2.25/2.46      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))) | 
% 2.25/2.46       ~ ((v2_compts_1 @ sk_B @ sk_A))),
% 2.25/2.46      inference('sup-', [status(thm)], ['61', '62'])).
% 2.25/2.46  thf('64', plain, (~ ((v2_compts_1 @ sk_B @ sk_A))),
% 2.25/2.46      inference('sat_resolution*', [status(thm)], ['29', '63'])).
% 2.25/2.46  thf('65', plain, (~ (v2_compts_1 @ sk_B @ sk_A)),
% 2.25/2.46      inference('simpl_trail', [status(thm)], ['28', '64'])).
% 2.25/2.46  thf('66', plain,
% 2.25/2.46      (~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 2.25/2.46          (k1_pre_topc @ sk_A @ sk_B))),
% 2.25/2.46      inference('clc', [status(thm)], ['26', '65'])).
% 2.25/2.46  thf('67', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.25/2.46      inference('demod', [status(thm)], ['10', '15'])).
% 2.25/2.46  thf('68', plain,
% 2.25/2.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('69', plain,
% 2.25/2.46      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.25/2.46         (~ (m1_pre_topc @ X19 @ X20)
% 2.25/2.46          | ~ (r1_tarski @ X21 @ (k2_struct_0 @ X19))
% 2.25/2.46          | ((sk_D @ X21 @ X19) = (X21))
% 2.25/2.46          | (v2_compts_1 @ X21 @ X20)
% 2.25/2.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.25/2.46          | ~ (l1_pre_topc @ X20))),
% 2.25/2.46      inference('cnf', [status(esa)], [t11_compts_1])).
% 2.25/2.46  thf('70', plain,
% 2.25/2.46      (![X0 : $i]:
% 2.25/2.46         (~ (l1_pre_topc @ sk_A)
% 2.25/2.46          | (v2_compts_1 @ sk_B @ sk_A)
% 2.25/2.46          | ((sk_D @ sk_B @ X0) = (sk_B))
% 2.25/2.46          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.25/2.46          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.25/2.46      inference('sup-', [status(thm)], ['68', '69'])).
% 2.25/2.46  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 2.25/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.46  thf('72', plain,
% 2.25/2.46      (![X0 : $i]:
% 2.25/2.46         ((v2_compts_1 @ sk_B @ sk_A)
% 2.25/2.46          | ((sk_D @ sk_B @ X0) = (sk_B))
% 2.25/2.46          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.25/2.46          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.25/2.46      inference('demod', [status(thm)], ['70', '71'])).
% 2.25/2.46  thf('73', plain,
% 2.25/2.46      ((~ (r1_tarski @ sk_B @ sk_B)
% 2.25/2.46        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.25/2.46        | ((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 2.25/2.46        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.25/2.46      inference('sup-', [status(thm)], ['67', '72'])).
% 2.25/2.46  thf('74', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.25/2.46      inference('simplify', [status(thm)], ['23'])).
% 2.25/2.46  thf('75', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.25/2.46      inference('demod', [status(thm)], ['13', '14'])).
% 2.25/2.46  thf('76', plain,
% 2.25/2.46      ((((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 2.25/2.46        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.25/2.46      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.25/2.46  thf('77', plain, (~ (v2_compts_1 @ sk_B @ sk_A)),
% 2.25/2.46      inference('simpl_trail', [status(thm)], ['28', '64'])).
% 2.25/2.46  thf('78', plain, (((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.25/2.46      inference('clc', [status(thm)], ['76', '77'])).
% 2.25/2.46  thf('79', plain,
% 2.25/2.46      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.25/2.46         <= (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 2.25/2.46      inference('split', [status(esa)], ['35'])).
% 2.25/2.46  thf('80', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.25/2.46      inference('demod', [status(thm)], ['10', '15'])).
% 2.25/2.46  thf('81', plain,
% 2.25/2.46      (![X18 : $i]:
% 2.25/2.46         (~ (v1_compts_1 @ X18)
% 2.25/2.46          | (v2_compts_1 @ (k2_struct_0 @ X18) @ X18)
% 2.25/2.46          | ~ (l1_pre_topc @ X18))),
% 2.25/2.46      inference('cnf', [status(esa)], [t10_compts_1])).
% 2.25/2.46  thf('82', plain,
% 2.25/2.46      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.25/2.46      inference('sup+', [status(thm)], ['80', '81'])).
% 2.25/2.46  thf('83', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.25/2.46      inference('demod', [status(thm)], ['57', '58'])).
% 2.25/2.46  thf('84', plain,
% 2.25/2.46      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 2.25/2.46        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.25/2.46      inference('demod', [status(thm)], ['82', '83'])).
% 2.25/2.46  thf('85', plain,
% 2.25/2.46      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.25/2.46         <= (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 2.25/2.46      inference('sup-', [status(thm)], ['79', '84'])).
% 2.25/2.46  thf('86', plain,
% 2.25/2.46      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))) | 
% 2.25/2.46       ((v2_compts_1 @ sk_B @ sk_A))),
% 2.25/2.46      inference('split', [status(esa)], ['35'])).
% 2.25/2.46  thf('87', plain, (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.25/2.46      inference('sat_resolution*', [status(thm)], ['29', '63', '86'])).
% 2.25/2.46  thf('88', plain, ((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.25/2.46      inference('simpl_trail', [status(thm)], ['85', '87'])).
% 2.25/2.46  thf('89', plain, ($false),
% 2.25/2.46      inference('demod', [status(thm)], ['66', '78', '88'])).
% 2.25/2.46  
% 2.25/2.46  % SZS output end Refutation
% 2.25/2.46  
% 2.25/2.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
