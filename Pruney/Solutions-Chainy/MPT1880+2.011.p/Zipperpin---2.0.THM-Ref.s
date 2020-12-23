%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lmOpXEfyqW

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 289 expanded)
%              Number of leaves         :   26 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  891 (3961 expanded)
%              Number of equality atoms :   32 (  46 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( m1_subset_1 @ ( sk_C @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k2_pre_topc @ X21 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( v2_tex_2 @ ( sk_C @ X17 @ X18 ) @ X18 )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( r1_tarski @ X17 @ ( sk_C @ X17 @ X18 ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_tops_1 @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X3 @ X2 @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
    = ( sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('51',plain,(
    r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_tops_1 @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v1_tops_1 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ( v1_tops_1 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('66',plain,(
    v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','66'])).

thf('68',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','51','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    = ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_B
    = ( sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( X17
       != ( sk_C @ X17 @ X18 ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_B
 != ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lmOpXEfyqW
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:08:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 99 iterations in 0.052s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(t48_tex_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.51             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51              ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.51                ( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t48_tex_2])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d7_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.51             ( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.51               ( ![C:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | ~ (v2_tex_2 @ X17 @ X18)
% 0.21/0.51          | (m1_subset_1 @ (sk_C @ X17 @ X18) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | (v3_tex_2 @ X17 @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.51  thf('7', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf(t41_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.51             ( ![C:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                 ( ( r1_tarski @ C @ B ) =>
% 0.21/0.51                   ( ( k9_subset_1 @
% 0.21/0.51                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.21/0.51                     ( C ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.51          | ~ (v2_tex_2 @ X20 @ X21)
% 0.21/0.51          | ~ (r1_tarski @ X22 @ X20)
% 0.21/0.51          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 0.21/0.51              (k2_pre_topc @ X21 @ X22)) = (X22))
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.51          | ~ (l1_pre_topc @ X21)
% 0.21/0.51          | ~ (v2_pre_topc @ X21)
% 0.21/0.51          | (v2_struct_0 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.21/0.51          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51          | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | ~ (v2_tex_2 @ X17 @ X18)
% 0.21/0.51          | (v2_tex_2 @ (sk_C @ X17 @ X18) @ X18)
% 0.21/0.51          | (v3_tex_2 @ X17 @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.51        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (((v3_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.51  thf('19', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain, ((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.21/0.51          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11', '12', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51            (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | ~ (v2_tex_2 @ X17 @ X18)
% 0.21/0.51          | (r1_tarski @ X17 @ (sk_C @ X17 @ X18))
% 0.21/0.51          | (v3_tex_2 @ X17 @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.51        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.51  thf('29', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d2_tops_3, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.51             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.51          | ~ (v1_tops_1 @ X15 @ X16)
% 0.21/0.51          | ((k2_pre_topc @ X16 @ X15) = (u1_struct_0 @ X16))
% 0.21/0.51          | ~ (l1_pre_topc @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain, (((k2_pre_topc @ sk_A @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51          (u1_struct_0 @ sk_A)) = (sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '30', '36'])).
% 0.21/0.51  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51         (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.21/0.51          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11', '12', '20'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51            (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A))) = (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.21/0.51          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51           = (k3_xboole_0 @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf(t4_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.51  thf(idempotence_k9_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (((k9_subset_1 @ X3 @ X2 @ X2) = (X2))
% 0.21/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.51      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (((k3_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51         = (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['45', '48'])).
% 0.21/0.51  thf(t17_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.51  thf('51', plain, ((r1_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.51          | ~ (v1_tops_1 @ X15 @ X16)
% 0.21/0.51          | ((k2_pre_topc @ X16 @ X15) = (u1_struct_0 @ X16))
% 0.21/0.51          | ~ (l1_pre_topc @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ((k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((((k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t79_tops_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.51          | ~ (v1_tops_1 @ X12 @ X13)
% 0.21/0.51          | ~ (r1_tarski @ X12 @ X14)
% 0.21/0.51          | (v1_tops_1 @ X14 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.51          | ~ (l1_pre_topc @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [t79_tops_1])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v1_tops_1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (r1_tarski @ sk_B @ X0)
% 0.21/0.51          | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('62', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.51          | (v1_tops_1 @ X0 @ sk_A)
% 0.21/0.51          | ~ (r1_tarski @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '63'])).
% 0.21/0.51  thf('65', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('66', plain, ((v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['56', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51          (u1_struct_0 @ sk_A)) = (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '51', '67'])).
% 0.21/0.51  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51         (u1_struct_0 @ sk_A)) = (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain, (((sk_B) = (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup+', [status(thm)], ['39', '70'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | ~ (v2_tex_2 @ X17 @ X18)
% 0.21/0.51          | ((X17) != (sk_C @ X17 @ X18))
% 0.21/0.51          | (v3_tex_2 @ X17 @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (v3_tex_2 @ sk_B @ sk_A)
% 0.21/0.51        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.21/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.51  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('76', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.51  thf('78', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('79', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['77', '78'])).
% 0.21/0.51  thf('80', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['71', '79'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
