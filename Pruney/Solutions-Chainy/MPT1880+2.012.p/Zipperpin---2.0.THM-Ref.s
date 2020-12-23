%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IU3xf9LsVQ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 165 expanded)
%              Number of leaves         :   28 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  694 (1990 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X4 @ X2 @ X3 )
        = ( k3_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_C @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','10'])).

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

thf('12',plain,(
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

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( v2_tex_2 @ ( sk_C @ X13 @ X14 ) @ X14 )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v1_tops_1 @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = ( k2_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','33','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k3_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','42'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('44',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('54',plain,
    ( ( k3_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('56',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['43','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( X13
       != ( sk_C @ X13 @ X14 ) )
      | ( v3_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_B
 != ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IU3xf9LsVQ
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 11:50:22 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 173 iterations in 0.106s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.56  thf(dt_k2_struct_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_struct_0 @ A ) =>
% 0.20/0.56       ( m1_subset_1 @
% 0.20/0.56         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (![X9 : $i]:
% 0.20/0.56         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.56          | ~ (l1_struct_0 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.20/0.56  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (((k9_subset_1 @ X4 @ X2 @ X3) = (k3_xboole_0 @ X2 @ X3))
% 0.20/0.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (l1_struct_0 @ X0)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0))
% 0.20/0.56              = (k3_xboole_0 @ X1 @ (k2_struct_0 @ X0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf(t48_tex_2, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.20/0.56             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.56            ( l1_pre_topc @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56              ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.20/0.56                ( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t48_tex_2])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d7_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.56             ( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.56               ( ![C:$i]:
% 0.20/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.56                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.56          | ~ (v2_tex_2 @ X13 @ X14)
% 0.20/0.56          | (m1_subset_1 @ (sk_C @ X13 @ X14) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.56          | (v3_tex_2 @ X13 @ X14)
% 0.20/0.56          | ~ (l1_pre_topc @ X14))),
% 0.20/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('8', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.56  thf('10', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf(t41_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.56             ( ![C:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                 ( ( r1_tarski @ C @ B ) =>
% 0.20/0.56                   ( ( k9_subset_1 @
% 0.20/0.56                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.20/0.56                     ( C ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.56          | ~ (v2_tex_2 @ X16 @ X17)
% 0.20/0.56          | ~ (r1_tarski @ X18 @ X16)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 0.20/0.56              (k2_pre_topc @ X17 @ X18)) = (X18))
% 0.20/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.56          | ~ (l1_pre_topc @ X17)
% 0.20/0.56          | ~ (v2_pre_topc @ X17)
% 0.20/0.56          | (v2_struct_0 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56          | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.56          | ~ (v2_tex_2 @ X13 @ X14)
% 0.20/0.56          | (v2_tex_2 @ (sk_C @ X13 @ X14) @ X14)
% 0.20/0.56          | (v3_tex_2 @ X13 @ X14)
% 0.20/0.56          | ~ (l1_pre_topc @ X14))),
% 0.20/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('20', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (((v3_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.56  thf('22', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('23', plain, ((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.56      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['13', '14', '15', '23'])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56            (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.56          | ~ (v2_tex_2 @ X13 @ X14)
% 0.20/0.56          | (r1_tarski @ X13 @ (sk_C @ X13 @ X14))
% 0.20/0.56          | (v3_tex_2 @ X13 @ X14)
% 0.20/0.56          | ~ (l1_pre_topc @ X14))),
% 0.20/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.56        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('30', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.56  thf('32', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('33', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d3_tops_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.56             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.56          | ~ (v1_tops_1 @ X11 @ X12)
% 0.20/0.56          | ((k2_pre_topc @ X12 @ X11) = (k2_struct_0 @ X12))
% 0.20/0.56          | ~ (l1_pre_topc @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.20/0.56        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.56  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('38', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('39', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56          (k2_struct_0 @ sk_A)) = (sk_B))
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['25', '33', '39'])).
% 0.20/0.56  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56         (k2_struct_0 @ sk_A)) = (sk_B))),
% 0.20/0.56      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      ((((k3_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (k2_struct_0 @ sk_A)) = (sk_B))
% 0.20/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup+', [status(thm)], ['2', '42'])).
% 0.20/0.56  thf(d3_struct_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X8 : $i]:
% 0.20/0.56         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf(t3_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.56  thf('47', plain, ((r1_tarski @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (((r1_tarski @ (sk_C @ sk_B @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.20/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup+', [status(thm)], ['44', '47'])).
% 0.20/0.56  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_l1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.56  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf('52', plain, ((r1_tarski @ (sk_C @ sk_B @ sk_A) @ (k2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['48', '51'])).
% 0.20/0.56  thf(t28_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      (((k3_xboole_0 @ (sk_C @ sk_B @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.20/0.56         = (sk_C @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.56  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf('56', plain, (((sk_C @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['43', '54', '55'])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.56          | ~ (v2_tex_2 @ X13 @ X14)
% 0.20/0.56          | ((X13) != (sk_C @ X13 @ X14))
% 0.20/0.56          | (v3_tex_2 @ X13 @ X14)
% 0.20/0.56          | ~ (l1_pre_topc @ X14))),
% 0.20/0.56      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | (v3_tex_2 @ sk_B @ sk_A)
% 0.39/0.56        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.39/0.56        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.56  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('61', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('62', plain,
% 0.39/0.56      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.39/0.56  thf('63', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('64', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.39/0.56      inference('clc', [status(thm)], ['62', '63'])).
% 0.39/0.56  thf('65', plain, ($false),
% 0.39/0.56      inference('simplify_reflect-', [status(thm)], ['56', '64'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
