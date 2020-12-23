%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zBKDjsFFYi

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:11 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 291 expanded)
%              Number of leaves         :   25 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  908 (3983 expanded)
%              Number of equality atoms :   32 (  46 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( m1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_pre_topc @ X20 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( v2_tex_2 @ ( sk_C @ X16 @ X17 ) @ X17 )
      | ( v3_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( r1_tarski @ X16 @ ( sk_C @ X16 @ X17 ) )
      | ( v3_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_tops_1 @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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

thf('43',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X3 @ X2 @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('50',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ X2 )
      = X2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
    = ( sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('53',plain,(
    r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_tops_1 @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v1_tops_1 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ( v1_tops_1 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('68',plain,(
    v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','68'])).

thf('70',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','53','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    = ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B
    = ( sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_tex_2 @ X16 @ X17 )
      | ( X16
       != ( sk_C @ X16 @ X17 ) )
      | ( v3_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_B
 != ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zBKDjsFFYi
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 171 iterations in 0.098s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.55  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.38/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.38/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.55  thf(t48_tex_2, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.38/0.55             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.55            ( l1_pre_topc @ A ) ) =>
% 0.38/0.55          ( ![B:$i]:
% 0.38/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55              ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.38/0.55                ( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t48_tex_2])).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(d7_tex_2, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( v3_tex_2 @ B @ A ) <=>
% 0.38/0.55             ( ( v2_tex_2 @ B @ A ) & 
% 0.38/0.55               ( ![C:$i]:
% 0.38/0.55                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.55                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.55          | ~ (v2_tex_2 @ X16 @ X17)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ X16 @ X17) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.55          | (v3_tex_2 @ X16 @ X17)
% 0.38/0.55          | ~ (l1_pre_topc @ X17))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.55        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('5', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (((v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.55        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.55  thf('7', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('clc', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf(t41_tex_2, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( v2_tex_2 @ B @ A ) <=>
% 0.38/0.55             ( ![C:$i]:
% 0.38/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55                 ( ( r1_tarski @ C @ B ) =>
% 0.38/0.55                   ( ( k9_subset_1 @
% 0.38/0.55                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.38/0.55                     ( C ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.55          | ~ (v2_tex_2 @ X19 @ X20)
% 0.38/0.55          | ~ (r1_tarski @ X21 @ X19)
% 0.38/0.55          | ((k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 0.38/0.55              (k2_pre_topc @ X20 @ X21)) = (X21))
% 0.38/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.55          | ~ (l1_pre_topc @ X20)
% 0.38/0.55          | ~ (v2_pre_topc @ X20)
% 0.38/0.55          | (v2_struct_0 @ X20))),
% 0.38/0.55      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.38/0.55          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.55          | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.55  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.55          | ~ (v2_tex_2 @ X16 @ X17)
% 0.38/0.55          | (v2_tex_2 @ (sk_C @ X16 @ X17) @ X17)
% 0.38/0.55          | (v3_tex_2 @ X16 @ X17)
% 0.38/0.55          | ~ (l1_pre_topc @ X17))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.55        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.55        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.55  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('17', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (((v3_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.38/0.55  thf('19', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('20', plain, ((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.38/0.55      inference('clc', [status(thm)], ['18', '19'])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.38/0.55          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)], ['10', '11', '12', '20'])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.55        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55            (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '21'])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.55          | ~ (v2_tex_2 @ X16 @ X17)
% 0.38/0.55          | (r1_tarski @ X16 @ (sk_C @ X16 @ X17))
% 0.38/0.55          | (v3_tex_2 @ X16 @ X17)
% 0.38/0.55          | ~ (l1_pre_topc @ X17))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.55        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.55        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.55  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.38/0.55  thf('29', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('30', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.38/0.55      inference('clc', [status(thm)], ['28', '29'])).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(d2_tops_3, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( v1_tops_1 @ B @ A ) <=>
% 0.38/0.55             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (![X14 : $i, X15 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.55          | ~ (v1_tops_1 @ X14 @ X15)
% 0.38/0.55          | ((k2_pre_topc @ X15 @ X14) = (u1_struct_0 @ X15))
% 0.38/0.55          | ~ (l1_pre_topc @ X15))),
% 0.38/0.55      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))
% 0.38/0.55        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.55  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('35', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('36', plain, (((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55          (u1_struct_0 @ sk_A)) = (sk_B))
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['22', '30', '36'])).
% 0.38/0.55  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55         (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.38/0.55      inference('clc', [status(thm)], ['37', '38'])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('clc', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.38/0.55          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)], ['10', '11', '12', '20'])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      ((~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.38/0.55        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55            (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A))) = (sk_C @ sk_B @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('clc', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf(redefinition_k9_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.55  thf('44', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.55         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.38/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.38/0.55  thf('45', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.38/0.55           = (k3_xboole_0 @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.55  thf(t17_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.55  thf('46', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.38/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.55  thf(t3_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('47', plain,
% 0.38/0.55      (![X8 : $i, X10 : $i]:
% 0.38/0.55         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('48', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.55  thf(idempotence_k9_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.38/0.55  thf('49', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.55         (((k9_subset_1 @ X3 @ X2 @ X2) = (X2))
% 0.38/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.38/0.55      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.38/0.55  thf('50', plain,
% 0.38/0.55      (![X0 : $i, X2 : $i]: ((k9_subset_1 @ X0 @ X2 @ X2) = (X2))),
% 0.38/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      (((k3_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.38/0.55         = (sk_C @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup+', [status(thm)], ['45', '50'])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.38/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.55  thf('53', plain, ((r1_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup+', [status(thm)], ['51', '52'])).
% 0.38/0.55  thf('54', plain,
% 0.38/0.55      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('clc', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      (![X14 : $i, X15 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.55          | ~ (v1_tops_1 @ X14 @ X15)
% 0.38/0.55          | ((k2_pre_topc @ X15 @ X14) = (u1_struct_0 @ X15))
% 0.38/0.55          | ~ (l1_pre_topc @ X15))),
% 0.38/0.55      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ((k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.38/0.55        | ~ (v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.55  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('58', plain,
% 0.38/0.55      ((((k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.38/0.55        | ~ (v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('clc', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t79_tops_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.55                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.38/0.55  thf('61', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.55          | ~ (v1_tops_1 @ X11 @ X12)
% 0.38/0.55          | ~ (r1_tarski @ X11 @ X13)
% 0.38/0.55          | (v1_tops_1 @ X13 @ X12)
% 0.38/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.55          | ~ (l1_pre_topc @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [t79_tops_1])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55          | (v1_tops_1 @ X0 @ sk_A)
% 0.38/0.55          | ~ (r1_tarski @ sk_B @ X0)
% 0.38/0.55          | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.55  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('64', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('65', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.55          | (v1_tops_1 @ X0 @ sk_A)
% 0.38/0.55          | ~ (r1_tarski @ sk_B @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.38/0.55  thf('66', plain,
% 0.38/0.55      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.55        | (v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['59', '65'])).
% 0.38/0.55  thf('67', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.38/0.55      inference('clc', [status(thm)], ['28', '29'])).
% 0.38/0.55  thf('68', plain, ((v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.38/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.38/0.55  thf('69', plain,
% 0.38/0.55      (((k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['58', '68'])).
% 0.38/0.55  thf('70', plain,
% 0.38/0.55      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55          (u1_struct_0 @ sk_A)) = (sk_C @ sk_B @ sk_A))
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['42', '53', '69'])).
% 0.38/0.55  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('72', plain,
% 0.38/0.55      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.38/0.55         (u1_struct_0 @ sk_A)) = (sk_C @ sk_B @ sk_A))),
% 0.38/0.55      inference('clc', [status(thm)], ['70', '71'])).
% 0.38/0.55  thf('73', plain, (((sk_B) = (sk_C @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup+', [status(thm)], ['39', '72'])).
% 0.38/0.55  thf('74', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('75', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.55          | ~ (v2_tex_2 @ X16 @ X17)
% 0.38/0.55          | ((X16) != (sk_C @ X16 @ X17))
% 0.38/0.55          | (v3_tex_2 @ X16 @ X17)
% 0.38/0.55          | ~ (l1_pre_topc @ X17))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.55  thf('76', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | (v3_tex_2 @ sk_B @ sk_A)
% 0.38/0.55        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.38/0.55        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['74', '75'])).
% 0.38/0.55  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('78', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('79', plain,
% 0.38/0.55      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.38/0.55      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.38/0.55  thf('80', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('81', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.38/0.55      inference('clc', [status(thm)], ['79', '80'])).
% 0.38/0.55  thf('82', plain, ($false),
% 0.38/0.55      inference('simplify_reflect-', [status(thm)], ['73', '81'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
