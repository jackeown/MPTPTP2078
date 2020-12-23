%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ALpkJXZSho

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 344 expanded)
%              Number of leaves         :   28 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          :  905 (3833 expanded)
%              Number of equality atoms :   20 ( 125 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t28_compts_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( C = D )
                   => ( ( v2_compts_1 @ C @ A )
                    <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( C = D )
                     => ( ( v2_compts_1 @ C @ A )
                      <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_compts_1])).

thf('0',plain,
    ( ~ ( v2_compts_1 @ sk_D_1 @ sk_B_1 )
    | ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ~ ( v2_compts_1 @ sk_D_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v2_compts_1 @ sk_D_1 @ sk_B_1 )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_compts_1 @ sk_D_1 @ sk_B_1 )
   <= ( v2_compts_1 @ sk_D_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_compts_1 @ sk_C @ sk_B_1 )
   <= ( v2_compts_1 @ sk_D_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(rc4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf(t79_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( v1_tops_1 @ C @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_tops_1 @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( v1_tops_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_tops_1 @ X1 @ X0 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ( v1_tops_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tops_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X17: $i] :
      ( ( v1_tops_1 @ ( sk_B @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc4_tops_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_tops_1 @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ X13 @ ( k2_pre_topc @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_B_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_B_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['25','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('45',plain,(
    r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ ( k2_struct_0 @ X21 ) )
      | ( ( sk_D @ X23 @ X21 )
        = X23 )
      | ( v2_compts_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C @ sk_A )
      | ( ( sk_D @ sk_C @ X0 )
        = sk_C )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C @ sk_A )
      | ( ( sk_D @ sk_C @ X0 )
        = sk_C )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( ( sk_D @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( sk_D @ sk_C @ sk_B_1 )
      = sk_C )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( ( sk_D @ sk_C @ sk_B_1 )
      = sk_C )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ ( k2_struct_0 @ X21 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X23 @ X21 ) @ X21 )
      | ( v2_compts_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ sk_B_1 ) @ sk_B_1 )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v2_compts_1 @ ( sk_D @ sk_C @ sk_B_1 ) @ sk_B_1 )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ~ ( v2_compts_1 @ sk_C @ sk_B_1 )
      | ( v2_compts_1 @ sk_C @ sk_A ) )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_A )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_B_1 )
   <= ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_compts_1 @ sk_C @ sk_A )
    | ~ ( v2_compts_1 @ sk_D_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','67'])).

thf('69',plain,
    ( ( v2_compts_1 @ sk_C @ sk_A )
    | ( v2_compts_1 @ sk_D_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('71',plain,
    ( ( v2_compts_1 @ sk_C @ sk_A )
   <= ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ ( k2_struct_0 @ X21 ) )
      | ~ ( v2_compts_1 @ X23 @ X22 )
      | ( X24 != X23 )
      | ( v2_compts_1 @ X24 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_compts_1 @ X23 @ X21 )
      | ~ ( v2_compts_1 @ X23 @ X22 )
      | ~ ( r1_tarski @ X23 @ ( k2_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_C @ sk_A )
      | ( v2_compts_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_C @ sk_A )
      | ( v2_compts_1 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_compts_1 @ sk_C @ X0 )
        | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A ) )
   <= ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf('79',plain,
    ( ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
      | ( v2_compts_1 @ sk_C @ sk_B_1 ) )
   <= ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    r1_tarski @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('82',plain,
    ( ( v2_compts_1 @ sk_C @ sk_B_1 )
   <= ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ~ ( v2_compts_1 @ sk_D_1 @ sk_B_1 )
   <= ~ ( v2_compts_1 @ sk_D_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_B_1 )
   <= ~ ( v2_compts_1 @ sk_D_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v2_compts_1 @ sk_D_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','68','69','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ALpkJXZSho
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 287 iterations in 0.088s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.19/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.19/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.54  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.54  thf(t28_compts_1, conjecture,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54               ( ![D:$i]:
% 0.19/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.54                   ( ( ( C ) = ( D ) ) =>
% 0.19/0.54                     ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i]:
% 0.19/0.54        ( ( l1_pre_topc @ A ) =>
% 0.19/0.54          ( ![B:$i]:
% 0.19/0.54            ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.54              ( ![C:$i]:
% 0.19/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54                  ( ![D:$i]:
% 0.19/0.54                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.54                      ( ( ( C ) = ( D ) ) =>
% 0.19/0.54                        ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t28_compts_1])).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      ((~ (v2_compts_1 @ sk_D_1 @ sk_B_1) | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      (~ ((v2_compts_1 @ sk_C @ sk_A)) | ~ ((v2_compts_1 @ sk_D_1 @ sk_B_1))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      (((v2_compts_1 @ sk_D_1 @ sk_B_1) | (v2_compts_1 @ sk_C @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('3', plain,
% 0.19/0.54      (((v2_compts_1 @ sk_D_1 @ sk_B_1)) <= (((v2_compts_1 @ sk_D_1 @ sk_B_1)))),
% 0.19/0.54      inference('split', [status(esa)], ['2'])).
% 0.19/0.54  thf('4', plain, (((sk_C) = (sk_D_1))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (((v2_compts_1 @ sk_C @ sk_B_1)) <= (((v2_compts_1 @ sk_D_1 @ sk_B_1)))),
% 0.19/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.54  thf(rc4_tops_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ?[B:$i]:
% 0.19/0.54         ( ( v1_tops_1 @ B @ A ) & 
% 0.19/0.54           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X17 : $i]:
% 0.19/0.54         ((m1_subset_1 @ (sk_B @ X17) @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.19/0.54          | ~ (l1_pre_topc @ X17))),
% 0.19/0.54      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.19/0.54  thf(t3_subset, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.54  thf('7', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i]:
% 0.19/0.54         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X0) | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.54  thf(dt_k2_subset_1, axiom,
% 0.19/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.54  thf('9', plain,
% 0.19/0.54      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.19/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.54  thf('10', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.19/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.54  thf('11', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.19/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.54  thf('12', plain,
% 0.19/0.54      (![X17 : $i]:
% 0.19/0.54         ((m1_subset_1 @ (sk_B @ X17) @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.19/0.54          | ~ (l1_pre_topc @ X17))),
% 0.19/0.54      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.19/0.54  thf(t79_tops_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.54                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.19/0.54  thf('13', plain,
% 0.19/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54          | ~ (v1_tops_1 @ X18 @ X19)
% 0.19/0.54          | ~ (r1_tarski @ X18 @ X20)
% 0.19/0.54          | (v1_tops_1 @ X20 @ X19)
% 0.19/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54          | ~ (l1_pre_topc @ X19))),
% 0.19/0.54      inference('cnf', [status(esa)], [t79_tops_1])).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X0)
% 0.19/0.54          | ~ (l1_pre_topc @ X0)
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.54          | (v1_tops_1 @ X1 @ X0)
% 0.19/0.54          | ~ (r1_tarski @ (sk_B @ X0) @ X1)
% 0.19/0.54          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         (~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.19/0.54          | ~ (r1_tarski @ (sk_B @ X0) @ X1)
% 0.19/0.54          | (v1_tops_1 @ X1 @ X0)
% 0.19/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.54          | ~ (l1_pre_topc @ X0))),
% 0.19/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.54  thf('16', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X0)
% 0.19/0.54          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.19/0.54          | ~ (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0))
% 0.19/0.54          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['11', '15'])).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X0)
% 0.19/0.54          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.19/0.54          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.19/0.54          | ~ (l1_pre_topc @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['8', '16'])).
% 0.19/0.54  thf('18', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.19/0.54          | ~ (v1_tops_1 @ (sk_B @ X0) @ X0)
% 0.19/0.54          | ~ (l1_pre_topc @ X0))),
% 0.19/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (![X17 : $i]: ((v1_tops_1 @ (sk_B @ X17) @ X17) | ~ (l1_pre_topc @ X17))),
% 0.19/0.54      inference('cnf', [status(esa)], [rc4_tops_1])).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.19/0.54      inference('clc', [status(thm)], ['18', '19'])).
% 0.19/0.54  thf('21', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.19/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.54  thf(d3_tops_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54           ( ( v1_tops_1 @ B @ A ) <=>
% 0.19/0.54             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.54  thf('22', plain,
% 0.19/0.54      (![X15 : $i, X16 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.54          | ~ (v1_tops_1 @ X15 @ X16)
% 0.19/0.54          | ((k2_pre_topc @ X16 @ X15) = (k2_struct_0 @ X16))
% 0.19/0.54          | ~ (l1_pre_topc @ X16))),
% 0.19/0.54      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X0)
% 0.19/0.54          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.19/0.54          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X0)
% 0.19/0.54          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.19/0.54          | ~ (l1_pre_topc @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['20', '23'])).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.19/0.54          | ~ (l1_pre_topc @ X0))),
% 0.19/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.54  thf('26', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.19/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.54  thf(t48_pre_topc, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.19/0.54  thf('27', plain,
% 0.19/0.54      (![X13 : $i, X14 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.19/0.54          | (r1_tarski @ X13 @ (k2_pre_topc @ X14 @ X13))
% 0.19/0.54          | ~ (l1_pre_topc @ X14))),
% 0.19/0.54      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.19/0.54  thf('28', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X0)
% 0.19/0.54          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.19/0.54             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.54  thf('29', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('30', plain, (((sk_C) = (sk_D_1))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.54  thf('32', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i]:
% 0.19/0.54         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.54  thf('33', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_B_1))),
% 0.19/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.54  thf(t1_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.54       ( r1_tarski @ A @ C ) ))).
% 0.19/0.54  thf('34', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.54          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.54          | (r1_tarski @ X0 @ X2))),
% 0.19/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.54  thf('35', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.54  thf('36', plain,
% 0.19/0.54      ((~ (l1_pre_topc @ sk_B_1)
% 0.19/0.54        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_B_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['28', '35'])).
% 0.19/0.54  thf('37', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(dt_m1_pre_topc, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.54  thf('38', plain,
% 0.19/0.54      (![X8 : $i, X9 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.19/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.54  thf('39', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.19/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.54  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('41', plain, ((l1_pre_topc @ sk_B_1)),
% 0.19/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.54  thf('42', plain,
% 0.19/0.54      ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_B_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.54      inference('demod', [status(thm)], ['36', '41'])).
% 0.19/0.54  thf('43', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k2_struct_0 @ sk_B_1)) | ~ (l1_pre_topc @ sk_B_1))),
% 0.19/0.54      inference('sup+', [status(thm)], ['25', '42'])).
% 0.19/0.54  thf('44', plain, ((l1_pre_topc @ sk_B_1)),
% 0.19/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.54  thf('45', plain, ((r1_tarski @ sk_C @ (k2_struct_0 @ sk_B_1))),
% 0.19/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.19/0.54  thf('46', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(t11_compts_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 0.19/0.54                 ( ( v2_compts_1 @ C @ A ) <=>
% 0.19/0.54                   ( ![D:$i]:
% 0.19/0.54                     ( ( m1_subset_1 @
% 0.19/0.54                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.54                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf('47', plain,
% 0.19/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X21 @ X22)
% 0.19/0.54          | ~ (r1_tarski @ X23 @ (k2_struct_0 @ X21))
% 0.19/0.54          | ((sk_D @ X23 @ X21) = (X23))
% 0.19/0.54          | (v2_compts_1 @ X23 @ X22)
% 0.19/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.19/0.54          | ~ (l1_pre_topc @ X22))),
% 0.19/0.54      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.19/0.54  thf('48', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ sk_A)
% 0.19/0.54          | (v2_compts_1 @ sk_C @ sk_A)
% 0.19/0.54          | ((sk_D @ sk_C @ X0) = (sk_C))
% 0.19/0.54          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.19/0.54          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.54  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('50', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_compts_1 @ sk_C @ sk_A)
% 0.19/0.54          | ((sk_D @ sk_C @ X0) = (sk_C))
% 0.19/0.54          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.19/0.54          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.19/0.54  thf('51', plain,
% 0.19/0.54      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.19/0.54        | ((sk_D @ sk_C @ sk_B_1) = (sk_C))
% 0.19/0.54        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['45', '50'])).
% 0.19/0.54  thf('52', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('53', plain,
% 0.19/0.54      ((((sk_D @ sk_C @ sk_B_1) = (sk_C)) | (v2_compts_1 @ sk_C @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.19/0.54  thf('54', plain,
% 0.19/0.54      ((~ (v2_compts_1 @ sk_C @ sk_A)) <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('55', plain,
% 0.19/0.54      ((((sk_D @ sk_C @ sk_B_1) = (sk_C))) <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.54  thf('56', plain, ((r1_tarski @ sk_C @ (k2_struct_0 @ sk_B_1))),
% 0.19/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.19/0.54  thf('57', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('58', plain,
% 0.19/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X21 @ X22)
% 0.19/0.54          | ~ (r1_tarski @ X23 @ (k2_struct_0 @ X21))
% 0.19/0.54          | ~ (v2_compts_1 @ (sk_D @ X23 @ X21) @ X21)
% 0.19/0.54          | (v2_compts_1 @ X23 @ X22)
% 0.19/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.19/0.54          | ~ (l1_pre_topc @ X22))),
% 0.19/0.54      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.19/0.54  thf('59', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ sk_A)
% 0.19/0.54          | (v2_compts_1 @ sk_C @ sk_A)
% 0.19/0.54          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 0.19/0.54          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.19/0.54          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.54  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('61', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_compts_1 @ sk_C @ sk_A)
% 0.19/0.54          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 0.19/0.54          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.19/0.54          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.19/0.54  thf('62', plain,
% 0.19/0.54      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.19/0.54        | ~ (v2_compts_1 @ (sk_D @ sk_C @ sk_B_1) @ sk_B_1)
% 0.19/0.54        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['56', '61'])).
% 0.19/0.54  thf('63', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('64', plain,
% 0.19/0.54      ((~ (v2_compts_1 @ (sk_D @ sk_C @ sk_B_1) @ sk_B_1)
% 0.19/0.54        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['62', '63'])).
% 0.19/0.54  thf('65', plain,
% 0.19/0.54      (((~ (v2_compts_1 @ sk_C @ sk_B_1) | (v2_compts_1 @ sk_C @ sk_A)))
% 0.19/0.54         <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['55', '64'])).
% 0.19/0.54  thf('66', plain,
% 0.19/0.54      ((~ (v2_compts_1 @ sk_C @ sk_A)) <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('67', plain,
% 0.19/0.54      ((~ (v2_compts_1 @ sk_C @ sk_B_1)) <= (~ ((v2_compts_1 @ sk_C @ sk_A)))),
% 0.19/0.54      inference('clc', [status(thm)], ['65', '66'])).
% 0.19/0.54  thf('68', plain,
% 0.19/0.54      (((v2_compts_1 @ sk_C @ sk_A)) | ~ ((v2_compts_1 @ sk_D_1 @ sk_B_1))),
% 0.19/0.54      inference('sup-', [status(thm)], ['5', '67'])).
% 0.19/0.54  thf('69', plain,
% 0.19/0.54      (((v2_compts_1 @ sk_C @ sk_A)) | ((v2_compts_1 @ sk_D_1 @ sk_B_1))),
% 0.19/0.54      inference('split', [status(esa)], ['2'])).
% 0.19/0.54  thf('70', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.54  thf('71', plain,
% 0.19/0.54      (((v2_compts_1 @ sk_C @ sk_A)) <= (((v2_compts_1 @ sk_C @ sk_A)))),
% 0.19/0.54      inference('split', [status(esa)], ['2'])).
% 0.19/0.54  thf('72', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('73', plain,
% 0.19/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X21 @ X22)
% 0.19/0.54          | ~ (r1_tarski @ X23 @ (k2_struct_0 @ X21))
% 0.19/0.54          | ~ (v2_compts_1 @ X23 @ X22)
% 0.19/0.54          | ((X24) != (X23))
% 0.19/0.54          | (v2_compts_1 @ X24 @ X21)
% 0.19/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.19/0.54          | ~ (l1_pre_topc @ X22))),
% 0.19/0.54      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.19/0.54  thf('74', plain,
% 0.19/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X22)
% 0.19/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.19/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.54          | (v2_compts_1 @ X23 @ X21)
% 0.19/0.54          | ~ (v2_compts_1 @ X23 @ X22)
% 0.19/0.54          | ~ (r1_tarski @ X23 @ (k2_struct_0 @ X21))
% 0.19/0.54          | ~ (m1_pre_topc @ X21 @ X22))),
% 0.19/0.54      inference('simplify', [status(thm)], ['73'])).
% 0.19/0.54  thf('75', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.54          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.19/0.54          | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.19/0.54          | (v2_compts_1 @ sk_C @ X0)
% 0.19/0.54          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.54          | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['72', '74'])).
% 0.19/0.54  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('77', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.54          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.19/0.54          | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.19/0.54          | (v2_compts_1 @ sk_C @ X0)
% 0.19/0.54          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.54      inference('demod', [status(thm)], ['75', '76'])).
% 0.19/0.54  thf('78', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.54           | (v2_compts_1 @ sk_C @ X0)
% 0.19/0.54           | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.19/0.54           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 0.19/0.54         <= (((v2_compts_1 @ sk_C @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['71', '77'])).
% 0.19/0.54  thf('79', plain,
% 0.19/0.54      (((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.19/0.54         | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ sk_B_1))
% 0.19/0.54         | (v2_compts_1 @ sk_C @ sk_B_1))) <= (((v2_compts_1 @ sk_C @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['70', '78'])).
% 0.19/0.54  thf('80', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('81', plain, ((r1_tarski @ sk_C @ (k2_struct_0 @ sk_B_1))),
% 0.19/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.19/0.54  thf('82', plain,
% 0.19/0.54      (((v2_compts_1 @ sk_C @ sk_B_1)) <= (((v2_compts_1 @ sk_C @ sk_A)))),
% 0.19/0.54      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.19/0.54  thf('83', plain,
% 0.19/0.54      ((~ (v2_compts_1 @ sk_D_1 @ sk_B_1))
% 0.19/0.54         <= (~ ((v2_compts_1 @ sk_D_1 @ sk_B_1)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('84', plain, (((sk_C) = (sk_D_1))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('85', plain,
% 0.19/0.54      ((~ (v2_compts_1 @ sk_C @ sk_B_1))
% 0.19/0.54         <= (~ ((v2_compts_1 @ sk_D_1 @ sk_B_1)))),
% 0.19/0.54      inference('demod', [status(thm)], ['83', '84'])).
% 0.19/0.54  thf('86', plain,
% 0.19/0.54      (~ ((v2_compts_1 @ sk_C @ sk_A)) | ((v2_compts_1 @ sk_D_1 @ sk_B_1))),
% 0.19/0.54      inference('sup-', [status(thm)], ['82', '85'])).
% 0.19/0.54  thf('87', plain, ($false),
% 0.19/0.54      inference('sat_resolution*', [status(thm)], ['1', '68', '69', '86'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
