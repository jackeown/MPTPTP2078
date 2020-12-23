%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9uJNNjOV2E

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:00 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  228 (2133 expanded)
%              Number of leaves         :   49 ( 631 expanded)
%              Depth                    :   27
%              Number of atoms          : 1736 (27457 expanded)
%              Number of equality atoms :   56 ( 650 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(t44_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ( v1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v2_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tex_2 @ X37 @ X38 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X37 @ X38 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( r1_tarski @ ( sk_C_2 @ X39 @ X40 ) @ X39 )
      | ( v2_tex_2 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tarski @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('19',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v1_zfmisc_1 @ X35 )
      | ( X36 = X35 )
      | ~ ( r1_tarski @ X36 @ X35 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('20',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
    | ( ( sk_C_2 @ sk_B_1 @ sk_A )
      = sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = sk_B_1 )
      | ( v1_xboole_0 @ ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('25',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 @ ( k2_pre_topc @ X40 @ ( sk_C_2 @ X39 @ X40 ) ) )
       != ( sk_C_2 @ X39 @ X40 ) )
      | ( v2_tex_2 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('26',plain,
    ( ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
       != ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X12 @ X14 @ X13 )
        = ( k9_subset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k3_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_1 )
      = ( k3_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ X27 @ ( k2_pre_topc @ X28 @ X27 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( sk_B_1
       != ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','33','34','41','42','43','44'])).

thf('46',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( sk_B_1
       != ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( ( sk_C_2 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('50',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 @ ( k2_pre_topc @ X40 @ ( sk_C_2 @ X39 @ X40 ) ) )
       != ( sk_C_2 @ X39 @ X40 ) )
      | ( v2_tex_2 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('51',plain,
    ( ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ k1_xboole_0 ) )
       != ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v4_pre_topc @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t52_pre_topc,axiom,(
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

thf('69',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k1_xboole_0
       != ( sk_C_2 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','74','75','78','79','80','81'])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( k1_xboole_0
       != ( sk_C_2 @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','83'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('91',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('93',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','91','92'])).

thf('94',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('101',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tex_2 @ X37 @ X38 )
      | ( m1_pre_topc @ ( sk_C_1 @ X37 @ X38 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('112',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('113',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf(cc2_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( v2_tdlat_3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) ) ) ) )).

thf('116',plain,(
    ! [X32: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( v1_tdlat_3 @ X32 )
      | ~ ( v2_tdlat_3 @ X32 )
      | ( v7_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('117',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('119',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tex_2 @ X37 @ X38 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X37 @ X38 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['117','129'])).

thf('131',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('132',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v2_tdlat_3 @ X33 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_tdlat_3 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','91','92'])).

thf('141',plain,(
    v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf(cc2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('143',plain,(
    ! [X31: $i] :
      ( ~ ( v2_tdlat_3 @ X31 )
      | ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc2_tdlat_3])).

thf('144',plain,
    ( ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('146',plain,
    ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','91','92'])).

thf('148',plain,(
    v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['130','141','148'])).

thf('150',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','91','92'])).

thf('151',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('153',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tex_2 @ X37 @ X38 )
      | ( X37
        = ( u1_struct_0 @ ( sk_C_1 @ X37 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['161','162'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('164',plain,(
    ! [X26: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ~ ( v7_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('165',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('167',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('168',plain,
    ( ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['165','168'])).

thf('170',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','91','92'])).

thf('171',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('173',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','91'])).

thf('174',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['171','174'])).

thf('176',plain,(
    v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['151','175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['99','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9uJNNjOV2E
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.44/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.69  % Solved by: fo/fo7.sh
% 0.44/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.69  % done 544 iterations in 0.250s
% 0.44/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.69  % SZS output start Refutation
% 0.44/0.69  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.44/0.69  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.44/0.69  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.44/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.69  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.44/0.69  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.44/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.69  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.44/0.69  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.44/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.69  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.44/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.69  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.44/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.69  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.69  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.44/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.69  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.69  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.44/0.69  thf(t44_tex_2, conjecture,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.44/0.69         ( l1_pre_topc @ A ) ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.69             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.69           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.44/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.69    (~( ![A:$i]:
% 0.44/0.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.69            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.69          ( ![B:$i]:
% 0.44/0.69            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.69                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.69              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.44/0.69    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.44/0.69  thf('0', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(t34_tex_2, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.69             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.69           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.44/0.69                ( ![C:$i]:
% 0.44/0.69                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.44/0.69                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.44/0.69                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.44/0.69  thf('1', plain,
% 0.44/0.69      (![X37 : $i, X38 : $i]:
% 0.44/0.69         ((v1_xboole_0 @ X37)
% 0.44/0.69          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.44/0.69          | ~ (v2_tex_2 @ X37 @ X38)
% 0.44/0.69          | ~ (v2_struct_0 @ (sk_C_1 @ X37 @ X38))
% 0.44/0.69          | ~ (l1_pre_topc @ X38)
% 0.44/0.69          | ~ (v2_pre_topc @ X38)
% 0.44/0.69          | (v2_struct_0 @ X38))),
% 0.44/0.69      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.44/0.69  thf('2', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.69        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.69  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('5', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.44/0.69  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('7', plain,
% 0.44/0.69      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('split', [status(esa)], ['6'])).
% 0.44/0.69  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('9', plain,
% 0.44/0.69      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('split', [status(esa)], ['8'])).
% 0.44/0.69  thf('10', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('split', [status(esa)], ['6'])).
% 0.44/0.69  thf('11', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(t41_tex_2, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.69           ( ( v2_tex_2 @ B @ A ) <=>
% 0.44/0.69             ( ![C:$i]:
% 0.44/0.69               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.69                 ( ( r1_tarski @ C @ B ) =>
% 0.44/0.69                   ( ( k9_subset_1 @
% 0.44/0.69                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.44/0.69                     ( C ) ) ) ) ) ) ) ) ))).
% 0.44/0.69  thf('12', plain,
% 0.44/0.69      (![X39 : $i, X40 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.44/0.69          | (r1_tarski @ (sk_C_2 @ X39 @ X40) @ X39)
% 0.44/0.69          | (v2_tex_2 @ X39 @ X40)
% 0.44/0.69          | ~ (l1_pre_topc @ X40)
% 0.44/0.69          | ~ (v2_pre_topc @ X40)
% 0.44/0.69          | (v2_struct_0 @ X40))),
% 0.44/0.69      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.44/0.69  thf('13', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.69        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (r1_tarski @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.69  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('16', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (r1_tarski @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.44/0.69      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.44/0.69  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('18', plain,
% 0.44/0.69      (((r1_tarski @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.44/0.69        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('clc', [status(thm)], ['16', '17'])).
% 0.44/0.69  thf(t1_tex_2, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.44/0.69           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.44/0.69  thf('19', plain,
% 0.44/0.69      (![X35 : $i, X36 : $i]:
% 0.44/0.69         ((v1_xboole_0 @ X35)
% 0.44/0.69          | ~ (v1_zfmisc_1 @ X35)
% 0.44/0.69          | ((X36) = (X35))
% 0.44/0.69          | ~ (r1_tarski @ X36 @ X35)
% 0.44/0.69          | (v1_xboole_0 @ X36))),
% 0.44/0.69      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.44/0.69  thf('20', plain,
% 0.44/0.69      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_xboole_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.44/0.69        | ((sk_C_2 @ sk_B_1 @ sk_A) = (sk_B_1))
% 0.44/0.69        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.69  thf('21', plain,
% 0.44/0.69      ((((v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (sk_B_1))
% 0.44/0.69         | (v1_xboole_0 @ (sk_C_2 @ sk_B_1 @ sk_A))
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['10', '20'])).
% 0.44/0.69  thf(l13_xboole_0, axiom,
% 0.44/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.69  thf('22', plain,
% 0.44/0.69      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 0.44/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.69  thf('23', plain,
% 0.44/0.69      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (sk_B_1))
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.44/0.69         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.69  thf('24', plain,
% 0.44/0.69      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (sk_B_1))
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.44/0.69         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.69  thf('25', plain,
% 0.44/0.69      (![X39 : $i, X40 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.44/0.69          | ((k9_subset_1 @ (u1_struct_0 @ X40) @ X39 @ 
% 0.44/0.69              (k2_pre_topc @ X40 @ (sk_C_2 @ X39 @ X40)))
% 0.44/0.69              != (sk_C_2 @ X39 @ X40))
% 0.44/0.69          | (v2_tex_2 @ X39 @ X40)
% 0.44/0.69          | ~ (l1_pre_topc @ X40)
% 0.44/0.69          | ~ (v2_pre_topc @ X40)
% 0.44/0.69          | (v2_struct_0 @ X40))),
% 0.44/0.69      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.44/0.69  thf('26', plain,
% 0.44/0.69      (((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.44/0.69           (k2_pre_topc @ sk_A @ sk_B_1)) != (sk_C_2 @ sk_B_1 @ sk_A))
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A)
% 0.44/0.69         | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.44/0.69         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.44/0.69  thf('27', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(commutativity_k9_subset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.44/0.69  thf('28', plain,
% 0.44/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.44/0.69         (((k9_subset_1 @ X12 @ X14 @ X13) = (k9_subset_1 @ X12 @ X13 @ X14))
% 0.44/0.69          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.44/0.69      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.44/0.69  thf('29', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B_1)
% 0.44/0.69           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.69  thf('30', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.69  thf('31', plain,
% 0.44/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.69         (((k9_subset_1 @ X17 @ X15 @ X16) = (k3_xboole_0 @ X15 @ X16))
% 0.44/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.44/0.69      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.69  thf('32', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B_1)
% 0.44/0.69           = (k3_xboole_0 @ X0 @ sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.69  thf('33', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k3_xboole_0 @ X0 @ sk_B_1)
% 0.44/0.69           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0))),
% 0.44/0.69      inference('demod', [status(thm)], ['29', '32'])).
% 0.44/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.69  thf('34', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.69  thf('35', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(t48_pre_topc, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( l1_pre_topc @ A ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.69           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.44/0.69  thf('36', plain,
% 0.44/0.69      (![X27 : $i, X28 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.44/0.69          | (r1_tarski @ X27 @ (k2_pre_topc @ X28 @ X27))
% 0.44/0.69          | ~ (l1_pre_topc @ X28))),
% 0.44/0.69      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.44/0.69  thf('37', plain,
% 0.44/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.69        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.69  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('39', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 0.44/0.69      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.69  thf(t28_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.69  thf('40', plain,
% 0.44/0.69      (![X10 : $i, X11 : $i]:
% 0.44/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.69  thf('41', plain,
% 0.44/0.69      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.69  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('44', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('45', plain,
% 0.44/0.69      (((((sk_B_1) != (sk_C_2 @ sk_B_1 @ sk_A))
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('demod', [status(thm)],
% 0.44/0.69                ['26', '33', '34', '41', '42', '43', '44'])).
% 0.44/0.69  thf('46', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.44/0.69         | ((sk_B_1) != (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('simplify', [status(thm)], ['45'])).
% 0.44/0.69  thf('47', plain,
% 0.44/0.69      (((((sk_B_1) != (sk_B_1))
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['23', '46'])).
% 0.44/0.69  thf('48', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.44/0.69         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('simplify', [status(thm)], ['47'])).
% 0.44/0.69  thf('49', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | ((sk_C_2 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.44/0.69         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('simplify', [status(thm)], ['47'])).
% 0.44/0.69  thf('50', plain,
% 0.44/0.69      (![X39 : $i, X40 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.44/0.69          | ((k9_subset_1 @ (u1_struct_0 @ X40) @ X39 @ 
% 0.44/0.69              (k2_pre_topc @ X40 @ (sk_C_2 @ X39 @ X40)))
% 0.44/0.69              != (sk_C_2 @ X39 @ X40))
% 0.44/0.69          | (v2_tex_2 @ X39 @ X40)
% 0.44/0.69          | ~ (l1_pre_topc @ X40)
% 0.44/0.69          | ~ (v2_pre_topc @ X40)
% 0.44/0.69          | (v2_struct_0 @ X40))),
% 0.44/0.69      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.44/0.69  thf('51', plain,
% 0.44/0.69      (((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.44/0.69           (k2_pre_topc @ sk_A @ k1_xboole_0)) != (sk_C_2 @ sk_B_1 @ sk_A))
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A)
% 0.44/0.69         | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.44/0.69         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.69  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(d3_tarski, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.69  thf('53', plain,
% 0.44/0.69      (![X6 : $i, X8 : $i]:
% 0.44/0.69         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.44/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.69  thf(d1_xboole_0, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.44/0.69  thf('54', plain,
% 0.44/0.69      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.44/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.69  thf('55', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.69  thf(t3_subset, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.69  thf('56', plain,
% 0.44/0.69      (![X18 : $i, X20 : $i]:
% 0.44/0.69         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.44/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.69  thf('57', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['55', '56'])).
% 0.44/0.69  thf(cc2_pre_topc, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.69           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.44/0.69  thf('58', plain,
% 0.44/0.69      (![X21 : $i, X22 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.44/0.69          | (v4_pre_topc @ X21 @ X22)
% 0.44/0.69          | ~ (v1_xboole_0 @ X21)
% 0.44/0.69          | ~ (l1_pre_topc @ X22)
% 0.44/0.69          | ~ (v2_pre_topc @ X22))),
% 0.44/0.69      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.44/0.69  thf('59', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         (~ (v1_xboole_0 @ X1)
% 0.44/0.69          | ~ (v2_pre_topc @ X0)
% 0.44/0.69          | ~ (l1_pre_topc @ X0)
% 0.44/0.69          | ~ (v1_xboole_0 @ X1)
% 0.44/0.69          | (v4_pre_topc @ X1 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.69  thf('60', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         ((v4_pre_topc @ X1 @ X0)
% 0.44/0.69          | ~ (l1_pre_topc @ X0)
% 0.44/0.69          | ~ (v2_pre_topc @ X0)
% 0.44/0.69          | ~ (v1_xboole_0 @ X1))),
% 0.44/0.69      inference('simplify', [status(thm)], ['59'])).
% 0.44/0.69  thf('61', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         (~ (v1_xboole_0 @ X0)
% 0.44/0.69          | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69          | (v4_pre_topc @ X0 @ sk_A))),
% 0.44/0.69      inference('sup-', [status(thm)], ['52', '60'])).
% 0.44/0.69  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('63', plain,
% 0.44/0.69      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.44/0.69      inference('demod', [status(thm)], ['61', '62'])).
% 0.44/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.69  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('65', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.69  thf('66', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.69      inference('sup-', [status(thm)], ['64', '65'])).
% 0.44/0.69  thf('67', plain,
% 0.44/0.69      (![X18 : $i, X20 : $i]:
% 0.44/0.69         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.44/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.69  thf('68', plain,
% 0.44/0.69      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.44/0.69  thf(t52_pre_topc, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( l1_pre_topc @ A ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.69           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.44/0.69             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.44/0.69               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.44/0.69  thf('69', plain,
% 0.44/0.69      (![X29 : $i, X30 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.44/0.69          | ~ (v4_pre_topc @ X29 @ X30)
% 0.44/0.69          | ((k2_pre_topc @ X30 @ X29) = (X29))
% 0.44/0.69          | ~ (l1_pre_topc @ X30))),
% 0.44/0.69      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.44/0.69  thf('70', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         (~ (l1_pre_topc @ X0)
% 0.44/0.69          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.44/0.69          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['68', '69'])).
% 0.44/0.69  thf('71', plain,
% 0.44/0.69      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.69        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.44/0.69        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.69      inference('sup-', [status(thm)], ['63', '70'])).
% 0.44/0.69  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.69  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('74', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.44/0.69  thf('75', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k3_xboole_0 @ X0 @ sk_B_1)
% 0.44/0.69           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0))),
% 0.44/0.69      inference('demod', [status(thm)], ['29', '32'])).
% 0.44/0.69  thf('76', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.69      inference('sup-', [status(thm)], ['64', '65'])).
% 0.44/0.69  thf('77', plain,
% 0.44/0.69      (![X10 : $i, X11 : $i]:
% 0.44/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.69  thf('78', plain,
% 0.44/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['76', '77'])).
% 0.44/0.69  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('81', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('82', plain,
% 0.44/0.69      (((((k1_xboole_0) != (sk_C_2 @ sk_B_1 @ sk_A))
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('demod', [status(thm)],
% 0.44/0.69                ['51', '74', '75', '78', '79', '80', '81'])).
% 0.44/0.69  thf('83', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | ((k1_xboole_0) != (sk_C_2 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('simplify', [status(thm)], ['82'])).
% 0.44/0.69  thf('84', plain,
% 0.44/0.69      (((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A)
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['48', '83'])).
% 0.44/0.69  thf('85', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A)
% 0.44/0.69         | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('simplify', [status(thm)], ['84'])).
% 0.44/0.69  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('87', plain,
% 0.44/0.69      ((((v1_xboole_0 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.44/0.69         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('clc', [status(thm)], ['85', '86'])).
% 0.44/0.69  thf('88', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('89', plain,
% 0.44/0.69      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('clc', [status(thm)], ['87', '88'])).
% 0.44/0.69  thf('90', plain,
% 0.44/0.69      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('split', [status(esa)], ['8'])).
% 0.44/0.69  thf('91', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['89', '90'])).
% 0.44/0.69  thf('92', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.44/0.69      inference('split', [status(esa)], ['6'])).
% 0.44/0.69  thf('93', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['9', '91', '92'])).
% 0.44/0.69  thf('94', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['7', '93'])).
% 0.44/0.69  thf('95', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('demod', [status(thm)], ['5', '94'])).
% 0.44/0.69  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('97', plain,
% 0.44/0.69      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['95', '96'])).
% 0.44/0.69  thf('98', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('99', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('clc', [status(thm)], ['97', '98'])).
% 0.44/0.69  thf('100', plain,
% 0.44/0.69      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('split', [status(esa)], ['6'])).
% 0.44/0.69  thf('101', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('102', plain,
% 0.44/0.69      (![X37 : $i, X38 : $i]:
% 0.44/0.69         ((v1_xboole_0 @ X37)
% 0.44/0.69          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.44/0.69          | ~ (v2_tex_2 @ X37 @ X38)
% 0.44/0.69          | (m1_pre_topc @ (sk_C_1 @ X37 @ X38) @ X38)
% 0.44/0.69          | ~ (l1_pre_topc @ X38)
% 0.44/0.69          | ~ (v2_pre_topc @ X38)
% 0.44/0.69          | (v2_struct_0 @ X38))),
% 0.44/0.69      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.44/0.69  thf('103', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.69        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.44/0.69        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['101', '102'])).
% 0.44/0.69  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('106', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.44/0.69        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.44/0.69  thf('107', plain,
% 0.44/0.69      ((((v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.44/0.69         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['100', '106'])).
% 0.44/0.69  thf('108', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('109', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['107', '108'])).
% 0.44/0.69  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('111', plain,
% 0.44/0.69      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['109', '110'])).
% 0.44/0.69  thf(dt_m1_pre_topc, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( l1_pre_topc @ A ) =>
% 0.44/0.69       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.44/0.69  thf('112', plain,
% 0.44/0.69      (![X24 : $i, X25 : $i]:
% 0.44/0.69         (~ (m1_pre_topc @ X24 @ X25)
% 0.44/0.69          | (l1_pre_topc @ X24)
% 0.44/0.69          | ~ (l1_pre_topc @ X25))),
% 0.44/0.69      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.44/0.69  thf('113', plain,
% 0.44/0.69      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['111', '112'])).
% 0.44/0.69  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('115', plain,
% 0.44/0.69      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('demod', [status(thm)], ['113', '114'])).
% 0.44/0.69  thf(cc2_tex_1, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( l1_pre_topc @ A ) =>
% 0.44/0.69       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.69           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.44/0.69         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.44/0.69  thf('116', plain,
% 0.44/0.69      (![X32 : $i]:
% 0.44/0.69         ((v2_struct_0 @ X32)
% 0.44/0.69          | ~ (v2_pre_topc @ X32)
% 0.44/0.69          | ~ (v1_tdlat_3 @ X32)
% 0.44/0.69          | ~ (v2_tdlat_3 @ X32)
% 0.44/0.69          | (v7_struct_0 @ X32)
% 0.44/0.69          | ~ (l1_pre_topc @ X32))),
% 0.44/0.69      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.44/0.69  thf('117', plain,
% 0.44/0.69      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['115', '116'])).
% 0.44/0.69  thf('118', plain,
% 0.44/0.69      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('split', [status(esa)], ['6'])).
% 0.44/0.69  thf('119', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('120', plain,
% 0.44/0.69      (![X37 : $i, X38 : $i]:
% 0.44/0.69         ((v1_xboole_0 @ X37)
% 0.44/0.69          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.44/0.69          | ~ (v2_tex_2 @ X37 @ X38)
% 0.44/0.69          | (v1_tdlat_3 @ (sk_C_1 @ X37 @ X38))
% 0.44/0.69          | ~ (l1_pre_topc @ X38)
% 0.44/0.69          | ~ (v2_pre_topc @ X38)
% 0.44/0.69          | (v2_struct_0 @ X38))),
% 0.44/0.69      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.44/0.69  thf('121', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.69        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['119', '120'])).
% 0.44/0.69  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('124', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.44/0.69  thf('125', plain,
% 0.44/0.69      ((((v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['118', '124'])).
% 0.44/0.69  thf('126', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('127', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['125', '126'])).
% 0.44/0.69  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('129', plain,
% 0.44/0.69      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['127', '128'])).
% 0.44/0.69  thf('130', plain,
% 0.44/0.69      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('demod', [status(thm)], ['117', '129'])).
% 0.44/0.69  thf('131', plain,
% 0.44/0.69      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['109', '110'])).
% 0.44/0.69  thf(cc6_tdlat_3, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.44/0.69         ( l1_pre_topc @ A ) ) =>
% 0.44/0.69       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.44/0.69  thf('132', plain,
% 0.44/0.69      (![X33 : $i, X34 : $i]:
% 0.44/0.69         (~ (m1_pre_topc @ X33 @ X34)
% 0.44/0.69          | (v2_tdlat_3 @ X33)
% 0.44/0.69          | ~ (l1_pre_topc @ X34)
% 0.44/0.69          | ~ (v2_tdlat_3 @ X34)
% 0.44/0.69          | ~ (v2_pre_topc @ X34)
% 0.44/0.69          | (v2_struct_0 @ X34))),
% 0.44/0.69      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.44/0.69  thf('133', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A)
% 0.44/0.69         | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69         | ~ (v2_tdlat_3 @ sk_A)
% 0.44/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.44/0.69         | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['131', '132'])).
% 0.44/0.69  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('135', plain, ((v2_tdlat_3 @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('137', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 0.44/0.69  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('139', plain,
% 0.44/0.69      (((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['137', '138'])).
% 0.44/0.69  thf('140', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['9', '91', '92'])).
% 0.44/0.69  thf('141', plain, ((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['139', '140'])).
% 0.44/0.69  thf('142', plain,
% 0.44/0.69      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('demod', [status(thm)], ['113', '114'])).
% 0.44/0.69  thf(cc2_tdlat_3, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( l1_pre_topc @ A ) => ( ( v2_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.44/0.69  thf('143', plain,
% 0.44/0.69      (![X31 : $i]:
% 0.44/0.69         (~ (v2_tdlat_3 @ X31) | (v2_pre_topc @ X31) | ~ (l1_pre_topc @ X31))),
% 0.44/0.69      inference('cnf', [status(esa)], [cc2_tdlat_3])).
% 0.44/0.69  thf('144', plain,
% 0.44/0.69      ((((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['142', '143'])).
% 0.44/0.69  thf('145', plain,
% 0.44/0.69      (((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['137', '138'])).
% 0.44/0.69  thf('146', plain,
% 0.44/0.69      (((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('demod', [status(thm)], ['144', '145'])).
% 0.44/0.69  thf('147', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['9', '91', '92'])).
% 0.44/0.69  thf('148', plain, ((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['146', '147'])).
% 0.44/0.69  thf('149', plain,
% 0.44/0.69      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('demod', [status(thm)], ['130', '141', '148'])).
% 0.44/0.69  thf('150', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['9', '91', '92'])).
% 0.44/0.69  thf('151', plain,
% 0.44/0.69      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['149', '150'])).
% 0.44/0.69  thf('152', plain,
% 0.44/0.69      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('split', [status(esa)], ['6'])).
% 0.44/0.69  thf('153', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('154', plain,
% 0.44/0.69      (![X37 : $i, X38 : $i]:
% 0.44/0.69         ((v1_xboole_0 @ X37)
% 0.44/0.69          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.44/0.69          | ~ (v2_tex_2 @ X37 @ X38)
% 0.44/0.69          | ((X37) = (u1_struct_0 @ (sk_C_1 @ X37 @ X38)))
% 0.44/0.69          | ~ (l1_pre_topc @ X38)
% 0.44/0.69          | ~ (v2_pre_topc @ X38)
% 0.44/0.69          | (v2_struct_0 @ X38))),
% 0.44/0.69      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.44/0.69  thf('155', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.44/0.69        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['153', '154'])).
% 0.44/0.69  thf('156', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('158', plain,
% 0.44/0.69      (((v2_struct_0 @ sk_A)
% 0.44/0.69        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.44/0.69        | (v1_xboole_0 @ sk_B_1))),
% 0.44/0.69      inference('demod', [status(thm)], ['155', '156', '157'])).
% 0.44/0.69  thf('159', plain,
% 0.44/0.69      ((((v1_xboole_0 @ sk_B_1)
% 0.44/0.69         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['152', '158'])).
% 0.44/0.69  thf('160', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('161', plain,
% 0.44/0.69      ((((v2_struct_0 @ sk_A)
% 0.44/0.69         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['159', '160'])).
% 0.44/0.69  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('163', plain,
% 0.44/0.69      ((((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('clc', [status(thm)], ['161', '162'])).
% 0.44/0.69  thf(fc7_struct_0, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.44/0.69       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.44/0.69  thf('164', plain,
% 0.44/0.69      (![X26 : $i]:
% 0.44/0.69         ((v1_zfmisc_1 @ (u1_struct_0 @ X26))
% 0.44/0.69          | ~ (l1_struct_0 @ X26)
% 0.44/0.69          | ~ (v7_struct_0 @ X26))),
% 0.44/0.69      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.44/0.69  thf('165', plain,
% 0.44/0.69      ((((v1_zfmisc_1 @ sk_B_1)
% 0.44/0.69         | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.44/0.69         | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('sup+', [status(thm)], ['163', '164'])).
% 0.44/0.69  thf('166', plain,
% 0.44/0.69      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('demod', [status(thm)], ['113', '114'])).
% 0.44/0.69  thf(dt_l1_pre_topc, axiom,
% 0.44/0.69    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.44/0.69  thf('167', plain,
% 0.44/0.69      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.44/0.69      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.69  thf('168', plain,
% 0.44/0.69      (((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['166', '167'])).
% 0.44/0.69  thf('169', plain,
% 0.44/0.69      ((((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.44/0.69         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('demod', [status(thm)], ['165', '168'])).
% 0.44/0.69  thf('170', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['9', '91', '92'])).
% 0.44/0.69  thf('171', plain,
% 0.44/0.69      (((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['169', '170'])).
% 0.44/0.69  thf('172', plain,
% 0.44/0.69      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.44/0.69      inference('split', [status(esa)], ['8'])).
% 0.44/0.69  thf('173', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['9', '91'])).
% 0.44/0.69  thf('174', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['172', '173'])).
% 0.44/0.69  thf('175', plain, (~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('clc', [status(thm)], ['171', '174'])).
% 0.44/0.69  thf('176', plain, ((v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.44/0.69      inference('clc', [status(thm)], ['151', '175'])).
% 0.44/0.69  thf('177', plain, ($false), inference('demod', [status(thm)], ['99', '176'])).
% 0.44/0.69  
% 0.44/0.69  % SZS output end Refutation
% 0.44/0.69  
% 0.52/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
