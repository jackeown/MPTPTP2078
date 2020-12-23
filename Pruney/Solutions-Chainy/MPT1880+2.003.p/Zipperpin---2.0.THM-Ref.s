%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PhGhBO9tYo

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:10 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 277 expanded)
%              Number of leaves         :   23 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          :  869 (3820 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(t48_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v1_tops_1 @ B @ A )
                & ( v2_tex_2 @ B @ A ) )
             => ( v3_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_C @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ~ ( r1_tarski @ X18 @ X16 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ ( k2_pre_topc @ X17 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( v2_tex_2 @ ( sk_C @ X13 @ X14 ) @ X14 )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v1_tops_1 @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','30','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','20'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
      = ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( r1_tarski @ ( k2_pre_topc @ X9 @ X8 ) @ ( k2_pre_topc @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('63',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','63'])).

thf('65',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','44','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    = ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_B
    = ( sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( X13
       != ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B
 != ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PhGhBO9tYo
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:20:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 329 iterations in 0.281s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.73  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.50/0.73  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.50/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.50/0.73  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.50/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.73  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.50/0.73  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.50/0.73  thf(t48_tex_2, conjecture,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.50/0.73             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i]:
% 0.50/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.50/0.73            ( l1_pre_topc @ A ) ) =>
% 0.50/0.73          ( ![B:$i]:
% 0.50/0.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73              ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.50/0.73                ( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t48_tex_2])).
% 0.50/0.73  thf('0', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('1', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(d7_tex_2, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( l1_pre_topc @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ( v3_tex_2 @ B @ A ) <=>
% 0.50/0.73             ( ( v2_tex_2 @ B @ A ) & 
% 0.50/0.73               ( ![C:$i]:
% 0.50/0.73                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.50/0.73                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.73  thf('2', plain,
% 0.50/0.73      (![X13 : $i, X14 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (v2_tex_2 @ X13 @ X14)
% 0.50/0.73          | (m1_subset_1 @ (sk_C @ X13 @ X14) @ 
% 0.50/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | (v3_tex_2 @ X13 @ X14)
% 0.50/0.73          | ~ (l1_pre_topc @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.73        | (v3_tex_2 @ sk_B @ sk_A)
% 0.50/0.73        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.73        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.73  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('5', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('6', plain,
% 0.50/0.73      (((v3_tex_2 @ sk_B @ sk_A)
% 0.50/0.73        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.73      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.50/0.73  thf('7', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('8', plain,
% 0.50/0.73      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('clc', [status(thm)], ['6', '7'])).
% 0.50/0.73  thf(t41_tex_2, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ( v2_tex_2 @ B @ A ) <=>
% 0.50/0.73             ( ![C:$i]:
% 0.50/0.73               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73                 ( ( r1_tarski @ C @ B ) =>
% 0.50/0.73                   ( ( k9_subset_1 @
% 0.50/0.73                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.50/0.73                     ( C ) ) ) ) ) ) ) ) ))).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.50/0.73          | ~ (v2_tex_2 @ X16 @ X17)
% 0.50/0.73          | ~ (r1_tarski @ X18 @ X16)
% 0.50/0.73          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 0.50/0.73              (k2_pre_topc @ X17 @ X18)) = (X18))
% 0.50/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.50/0.73          | ~ (l1_pre_topc @ X17)
% 0.50/0.73          | ~ (v2_pre_topc @ X17)
% 0.50/0.73          | (v2_struct_0 @ X17))),
% 0.50/0.73      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.50/0.73  thf('10', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((v2_struct_0 @ sk_A)
% 0.50/0.73          | ~ (v2_pre_topc @ sk_A)
% 0.50/0.73          | ~ (l1_pre_topc @ sk_A)
% 0.50/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.73          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.50/0.73          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.50/0.73          | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.73  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('13', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('14', plain,
% 0.50/0.73      (![X13 : $i, X14 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (v2_tex_2 @ X13 @ X14)
% 0.50/0.73          | (v2_tex_2 @ (sk_C @ X13 @ X14) @ X14)
% 0.50/0.73          | (v3_tex_2 @ X13 @ X14)
% 0.50/0.73          | ~ (l1_pre_topc @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.50/0.73  thf('15', plain,
% 0.50/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.73        | (v3_tex_2 @ sk_B @ sk_A)
% 0.50/0.73        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.50/0.73        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.50/0.73  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('17', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('18', plain,
% 0.50/0.73      (((v3_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.50/0.73  thf('19', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('20', plain, ((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.50/0.73      inference('clc', [status(thm)], ['18', '19'])).
% 0.50/0.73  thf('21', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((v2_struct_0 @ sk_A)
% 0.50/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.73          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.50/0.73          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['10', '11', '12', '20'])).
% 0.50/0.73  thf('22', plain,
% 0.50/0.73      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.50/0.73        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73            (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.50/0.73        | (v2_struct_0 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['0', '21'])).
% 0.50/0.73  thf('23', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('24', plain,
% 0.50/0.73      (![X13 : $i, X14 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.73          | ~ (v2_tex_2 @ X13 @ X14)
% 0.50/0.73          | (r1_tarski @ X13 @ (sk_C @ X13 @ X14))
% 0.50/0.73          | (v3_tex_2 @ X13 @ X14)
% 0.50/0.73          | ~ (l1_pre_topc @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.50/0.73  thf('25', plain,
% 0.50/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.73        | (v3_tex_2 @ sk_B @ sk_A)
% 0.50/0.73        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.50/0.73        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.73  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('28', plain,
% 0.50/0.73      (((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.50/0.73  thf('29', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('30', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.50/0.73      inference('clc', [status(thm)], ['28', '29'])).
% 0.50/0.73  thf('31', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(d2_tops_3, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( l1_pre_topc @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ( v1_tops_1 @ B @ A ) <=>
% 0.50/0.73             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.50/0.73  thf('32', plain,
% 0.50/0.73      (![X11 : $i, X12 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.50/0.73          | ~ (v1_tops_1 @ X11 @ X12)
% 0.50/0.73          | ((k2_pre_topc @ X12 @ X11) = (u1_struct_0 @ X12))
% 0.50/0.73          | ~ (l1_pre_topc @ X12))),
% 0.50/0.73      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.50/0.73  thf('33', plain,
% 0.50/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.73        | ((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))
% 0.50/0.73        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.73  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('35', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('36', plain, (((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.50/0.73  thf('37', plain,
% 0.50/0.73      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73          (u1_struct_0 @ sk_A)) = (sk_B))
% 0.50/0.73        | (v2_struct_0 @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['22', '30', '36'])).
% 0.50/0.73  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('39', plain,
% 0.50/0.73      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73         (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.50/0.73      inference('clc', [status(thm)], ['37', '38'])).
% 0.50/0.73  thf('40', plain,
% 0.50/0.73      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('clc', [status(thm)], ['6', '7'])).
% 0.50/0.73  thf('41', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((v2_struct_0 @ sk_A)
% 0.50/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.73          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.50/0.73          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['10', '11', '12', '20'])).
% 0.50/0.73  thf('42', plain,
% 0.50/0.73      ((~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.50/0.73        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73            (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A))) = (sk_C @ sk_B @ sk_A))
% 0.50/0.73        | (v2_struct_0 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['40', '41'])).
% 0.50/0.73  thf(d10_xboole_0, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.73  thf('43', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.73  thf('44', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.50/0.73      inference('simplify', [status(thm)], ['43'])).
% 0.50/0.73  thf('45', plain,
% 0.50/0.73      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('clc', [status(thm)], ['6', '7'])).
% 0.50/0.73  thf(dt_k2_pre_topc, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( l1_pre_topc @ A ) & 
% 0.50/0.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.73       ( m1_subset_1 @
% 0.50/0.73         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.50/0.73  thf('46', plain,
% 0.50/0.73      (![X6 : $i, X7 : $i]:
% 0.50/0.73         (~ (l1_pre_topc @ X6)
% 0.50/0.73          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.50/0.73          | (m1_subset_1 @ (k2_pre_topc @ X6 @ X7) @ 
% 0.50/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 0.50/0.73      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.50/0.73  thf('47', plain,
% 0.50/0.73      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) @ 
% 0.50/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.73  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('49', plain,
% 0.50/0.73      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) @ 
% 0.50/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['47', '48'])).
% 0.50/0.73  thf(t3_subset, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.73  thf('50', plain,
% 0.50/0.73      (![X3 : $i, X4 : $i]:
% 0.50/0.73         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.73  thf('51', plain,
% 0.50/0.73      ((r1_tarski @ (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) @ 
% 0.50/0.73        (u1_struct_0 @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['49', '50'])).
% 0.50/0.73  thf('52', plain,
% 0.50/0.73      (![X0 : $i, X2 : $i]:
% 0.50/0.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.73  thf('53', plain,
% 0.50/0.73      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.73           (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)))
% 0.50/0.73        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['51', '52'])).
% 0.50/0.73  thf('54', plain,
% 0.50/0.73      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('clc', [status(thm)], ['6', '7'])).
% 0.50/0.73  thf('55', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(t49_pre_topc, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( l1_pre_topc @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73           ( ![C:$i]:
% 0.50/0.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.73               ( ( r1_tarski @ B @ C ) =>
% 0.50/0.73                 ( r1_tarski @
% 0.50/0.73                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.50/0.73  thf('56', plain,
% 0.50/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.50/0.73          | ~ (r1_tarski @ X8 @ X10)
% 0.50/0.73          | (r1_tarski @ (k2_pre_topc @ X9 @ X8) @ (k2_pre_topc @ X9 @ X10))
% 0.50/0.73          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.50/0.73          | ~ (l1_pre_topc @ X9))),
% 0.50/0.73      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.50/0.73  thf('57', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (l1_pre_topc @ sk_A)
% 0.50/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.73          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.50/0.73             (k2_pre_topc @ sk_A @ X0))
% 0.50/0.73          | ~ (r1_tarski @ sk_B @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['55', '56'])).
% 0.50/0.73  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('59', plain, (((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.50/0.73  thf('60', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.73          | (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 0.50/0.73          | ~ (r1_tarski @ sk_B @ X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.50/0.73  thf('61', plain,
% 0.50/0.73      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.50/0.73        | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.73           (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['54', '60'])).
% 0.50/0.73  thf('62', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.50/0.73      inference('clc', [status(thm)], ['28', '29'])).
% 0.50/0.73  thf('63', plain,
% 0.50/0.73      ((r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.73        (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['61', '62'])).
% 0.50/0.73  thf('64', plain,
% 0.50/0.73      (((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['53', '63'])).
% 0.50/0.73  thf('65', plain,
% 0.50/0.73      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.73          (u1_struct_0 @ sk_A)) = (sk_C @ sk_B @ sk_A))
% 0.50/0.73        | (v2_struct_0 @ sk_A))),
% 0.50/0.73      inference('demod', [status(thm)], ['42', '44', '64'])).
% 0.50/0.73  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('67', plain,
% 0.50/0.74      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.50/0.74         (u1_struct_0 @ sk_A)) = (sk_C @ sk_B @ sk_A))),
% 0.50/0.74      inference('clc', [status(thm)], ['65', '66'])).
% 0.50/0.74  thf('68', plain, (((sk_B) = (sk_C @ sk_B @ sk_A))),
% 0.50/0.74      inference('sup+', [status(thm)], ['39', '67'])).
% 0.50/0.74  thf('69', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('70', plain,
% 0.50/0.74      (![X13 : $i, X14 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.50/0.74          | ~ (v2_tex_2 @ X13 @ X14)
% 0.50/0.74          | ((X13) != (sk_C @ X13 @ X14))
% 0.50/0.74          | (v3_tex_2 @ X13 @ X14)
% 0.50/0.74          | ~ (l1_pre_topc @ X14))),
% 0.50/0.74      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.50/0.74  thf('71', plain,
% 0.50/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.74        | (v3_tex_2 @ sk_B @ sk_A)
% 0.50/0.74        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.50/0.74        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.50/0.74      inference('sup-', [status(thm)], ['69', '70'])).
% 0.50/0.74  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('73', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('74', plain,
% 0.50/0.74      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.50/0.74      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.50/0.74  thf('75', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('76', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.50/0.74      inference('clc', [status(thm)], ['74', '75'])).
% 0.50/0.74  thf('77', plain, ($false),
% 0.50/0.74      inference('simplify_reflect-', [status(thm)], ['68', '76'])).
% 0.50/0.74  
% 0.50/0.74  % SZS output end Refutation
% 0.50/0.74  
% 0.58/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
