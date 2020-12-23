%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1121+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XfwIGlZsXo

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:05 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 412 expanded)
%              Number of leaves         :   24 ( 116 expanded)
%              Depth                    :   22
%              Number of atoms          : 1160 (6578 expanded)
%              Number of equality atoms :   30 ( 380 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t52_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v4_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ B )
                  = B ) )
              & ( ( ( v2_pre_topc @ A )
                  & ( ( k2_pre_topc @ A @ B )
                    = B ) )
               => ( v4_pre_topc @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_pre_topc])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ X21 @ ( k2_pre_topc @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( v4_pre_topc @ D @ A )
                        & ( r1_tarski @ B @ D ) )
                     => ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k2_pre_topc @ X15 @ X14 ) )
      | ~ ( v4_pre_topc @ X17 @ X15 )
      | ~ ( r1_tarski @ X14 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( r1_tarski @ sk_B @ sk_B )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ( v2_pre_topc @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('22',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ? [C: $i] :
              ( ( ( k2_pre_topc @ A @ B )
                = ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ C ) )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ D @ C )
                  <=> ( ( v4_pre_topc @ D @ A )
                      & ( r1_tarski @ B @ D ) ) ) )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( sk_C_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('25',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t44_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) )
           => ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( m1_subset_1 @ ( sk_C_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('30',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( k6_setfam_1 @ ( u1_struct_0 @ X19 ) @ ( sk_C_2 @ X18 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('37',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ X20 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( sk_C_2 @ X18 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X13 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('52',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('57',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['49','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ~ ( v4_pre_topc @ ( sk_C_1 @ X12 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('61',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ~ ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('66',plain,
    ( ( ~ ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['58','66'])).

thf('68',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','67'])).

thf('69',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('70',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('72',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['18','20','70','71'])).

thf('73',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['16','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','73','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('79',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('83',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['76','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','86'])).

thf('88',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','90'])).

thf('92',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('93',plain,(
    ( k2_pre_topc @ sk_A @ sk_B )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['18','20','70'])).

thf('94',plain,(
    ( k2_pre_topc @ sk_A @ sk_B )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','94'])).


%------------------------------------------------------------------------------
