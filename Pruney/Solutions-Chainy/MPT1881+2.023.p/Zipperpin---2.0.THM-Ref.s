%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SbtWEEbVI2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  213 (1025 expanded)
%              Number of leaves         :   36 ( 305 expanded)
%              Depth                    :   19
%              Number of atoms          : 1755 (12283 expanded)
%              Number of equality atoms :   68 ( 207 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tex_2 @ B @ A ) )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v1_tops_1 @ X27 @ X28 )
      | ~ ( v3_tex_2 @ X27 @ X28 )
      | ~ ( v3_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_tdlat_3 @ X20 )
      | ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('11',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_pre_topc @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','8','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v1_tops_1 @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = ( k2_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('36',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X3 ) @ X3 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

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

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_pre_topc @ X23 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_2 ) )
      = sk_B_2 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_2 ) )
      = sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_2 ) )
      = sk_B_2 )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ~ ( v2_tex_2 @ ( k2_struct_0 @ sk_A ) @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_2 ) )
        = sk_B_2 ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','52'])).

thf('54',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('55',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v1_tdlat_3 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( v2_tex_2 @ ( k2_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_tex_2 @ ( k2_struct_0 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_tex_2 @ ( k2_struct_0 @ sk_A ) @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('66',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('67',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('68',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X1 @ X0 @ X0 )
        = X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['53','64','65','66','67','70'])).

thf(fc12_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('72',plain,(
    ! [X11: $i] :
      ( ( v1_tops_1 @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc12_tops_1])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('73',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('77',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

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

thf('78',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v1_tops_1 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ( v1_tops_1 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_tops_1 @ X1 @ X0 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('85',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('93',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('94',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v1_tops_1 @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = ( k2_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ( ( v1_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( ( v3_tex_2 @ sk_B_2 @ sk_A )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['71','103'])).

thf('105',plain,(
    ! [X3: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X3 ) @ X3 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('107',plain,(
    ! [X3: $i] :
      ~ ( v1_subset_1 @ X3 @ X3 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('110',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('112',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('114',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('116',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_tex_2 @ X29 @ X30 )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ~ ( v1_tops_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ~ ( v1_tops_1 @ sk_B_2 @ sk_A )
      | ( v3_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('120',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('121',plain,
    ( ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('126',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('127',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k2_pre_topc @ X10 @ X9 )
       != ( k2_struct_0 @ X10 ) )
      | ( v1_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( k2_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( k2_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','130'])).

thf('132',plain,(
    ! [X11: $i] :
      ( ( v1_tops_1 @ ( k2_struct_0 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc12_tops_1])).

thf('133',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('134',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('135',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v1_tops_1 @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = ( k2_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('136',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = ( k2_struct_0 @ sk_A ) )
        | ~ ( v1_tops_1 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = ( k2_struct_0 @ sk_A ) )
        | ~ ( v1_tops_1 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ~ ( v1_tops_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','142'])).

thf('144',plain,
    ( ( v1_tops_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('146',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('147',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_tops_1 @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_tops_1 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('151',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = sk_B_2 )
        | ~ ( v1_tops_1 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( ~ ( v1_tops_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,
    ( ( v1_tops_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('154',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('155',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_B_2 )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','155'])).

thf('157',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('158',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('159',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v1_tdlat_3 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( v3_tex_2 @ sk_B_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','156','157','158','167','168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('174',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','108','109','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SbtWEEbVI2
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 324 iterations in 0.134s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.57  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.57  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.57  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(t49_tex_2, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.57         ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.57             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.57            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57              ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.57                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 0.21/0.57       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (((v3_tex_2 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t47_tex_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.21/0.57             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X27 : $i, X28 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.57          | (v1_tops_1 @ X27 @ X28)
% 0.21/0.57          | ~ (v3_tex_2 @ X27 @ X28)
% 0.21/0.57          | ~ (v3_pre_topc @ X27 @ X28)
% 0.21/0.57          | ~ (l1_pre_topc @ X28)
% 0.21/0.57          | ~ (v2_pre_topc @ X28)
% 0.21/0.57          | (v2_struct_0 @ X28))),
% 0.21/0.57      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.57        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.21/0.57        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t17_tdlat_3, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ( v1_tdlat_3 @ A ) <=>
% 0.21/0.57         ( ![B:$i]:
% 0.21/0.57           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X20 : $i, X21 : $i]:
% 0.21/0.57         (~ (v1_tdlat_3 @ X20)
% 0.21/0.57          | (v3_pre_topc @ X21 @ X20)
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.57          | ~ (l1_pre_topc @ X20)
% 0.21/0.57          | ~ (v2_pre_topc @ X20))),
% 0.21/0.57      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.21/0.57        | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('14', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('15', plain, ((v3_pre_topc @ sk_B_2 @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.21/0.57        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '7', '8', '15'])).
% 0.21/0.57  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d3_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.57             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.57          | ~ (v1_tops_1 @ X9 @ X10)
% 0.21/0.57          | ((k2_pre_topc @ X10 @ X9) = (k2_struct_0 @ X10))
% 0.21/0.57          | ~ (l1_pre_topc @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | ((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A))
% 0.21/0.57        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A))
% 0.21/0.57        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '18'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d2_tops_3, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.57             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57          | ~ (v1_tops_1 @ X16 @ X17)
% 0.21/0.57          | ((k2_pre_topc @ X17 @ X16) = (u1_struct_0 @ X17))
% 0.21/0.57          | ~ (l1_pre_topc @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.57        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.57  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.21/0.57        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '31'])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['25', '32'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(rc3_subset_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ?[B:$i]:
% 0.21/0.57       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.21/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.57  thf(d7_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.57       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (((X19) = (X18))
% 0.21/0.57          | (v1_subset_1 @ X19 @ X18)
% 0.21/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.57  thf('39', plain, (![X3 : $i]: ~ (v1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.21/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.57  thf('40', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.57  thf('41', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.57  thf(t41_tex_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.57             ( ![C:$i]:
% 0.21/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                 ( ( r1_tarski @ C @ B ) =>
% 0.21/0.57                   ( ( k9_subset_1 @
% 0.21/0.57                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.21/0.57                     ( C ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57          | ~ (v2_tex_2 @ X22 @ X23)
% 0.21/0.57          | ~ (r1_tarski @ X24 @ X22)
% 0.21/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.21/0.57              (k2_pre_topc @ X23 @ X24)) = (X24))
% 0.21/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.57          | ~ (l1_pre_topc @ X23)
% 0.21/0.57          | ~ (v2_pre_topc @ X23)
% 0.21/0.57          | (v2_struct_0 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.21/0.57              (k2_pre_topc @ X0 @ X1)) = (X1))
% 0.21/0.57          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57        | ~ (r1_tarski @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57            (k2_pre_topc @ sk_A @ sk_B_2)) = (sk_B_2))
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57        | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['34', '43'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t3_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('47', plain, ((r1_tarski @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.57  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57            (k2_pre_topc @ sk_A @ sk_B_2)) = (sk_B_2))
% 0.21/0.57        | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['44', '47', '48', '49'])).
% 0.21/0.57  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_pre_topc @ sk_A @ sk_B_2)) = (sk_B_2))
% 0.21/0.57        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.57      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (((~ (v2_tex_2 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57         | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57             (k2_pre_topc @ sk_A @ sk_B_2)) = (sk_B_2))))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['33', '52'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['25', '32'])).
% 0.21/0.57  thf('55', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.57  thf(t43_tex_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.57         ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X25 : $i, X26 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.57          | (v2_tex_2 @ X25 @ X26)
% 0.21/0.57          | ~ (l1_pre_topc @ X26)
% 0.21/0.57          | ~ (v1_tdlat_3 @ X26)
% 0.21/0.57          | ~ (v2_pre_topc @ X26)
% 0.21/0.57          | (v2_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.57  thf('58', plain,
% 0.21/0.57      ((((v2_tex_2 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57         | (v2_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['54', '57'])).
% 0.21/0.57  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('60', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      ((((v2_tex_2 @ (k2_struct_0 @ sk_A) @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.21/0.57  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      (((v2_tex_2 @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['25', '32'])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['25', '32'])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      ((((k2_pre_topc @ sk_A @ sk_B_2) = (k2_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '24'])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.57  thf(idempotence_k9_subset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.57       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (((k9_subset_1 @ X1 @ X0 @ X0) = (X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.57      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['53', '64', '65', '66', '67', '70'])).
% 0.21/0.57  thf(fc12_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) => ( v1_tops_1 @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (![X11 : $i]:
% 0.21/0.57         ((v1_tops_1 @ (k2_struct_0 @ X11) @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc12_tops_1])).
% 0.21/0.57  thf(dt_k2_struct_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_struct_0 @ A ) =>
% 0.21/0.57       ( m1_subset_1 @
% 0.21/0.57         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      (![X7 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.57          | ~ (l1_struct_0 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_struct_0 @ X0)
% 0.21/0.57          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.57  thf('76', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.57  thf('77', plain,
% 0.21/0.57      (![X7 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.57          | ~ (l1_struct_0 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.57  thf(t79_tops_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.57                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.57  thf('78', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | ~ (v1_tops_1 @ X12 @ X13)
% 0.21/0.57          | ~ (r1_tarski @ X12 @ X14)
% 0.21/0.57          | (v1_tops_1 @ X14 @ X13)
% 0.21/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | ~ (l1_pre_topc @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [t79_tops_1])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (l1_struct_0 @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.57          | (v1_tops_1 @ X1 @ X0)
% 0.21/0.57          | ~ (r1_tarski @ (k2_struct_0 @ X0) @ X1)
% 0.21/0.57          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.57  thf('80', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.21/0.57          | ~ (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.21/0.57          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_struct_0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['76', '79'])).
% 0.21/0.57  thf('81', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_struct_0 @ X0)
% 0.21/0.57          | ~ (l1_struct_0 @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.57          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['75', '80'])).
% 0.21/0.57  thf('82', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.21/0.57          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_struct_0 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['81'])).
% 0.21/0.57  thf('83', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_struct_0 @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['72', '82'])).
% 0.21/0.57  thf('84', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.57          | ~ (l1_struct_0 @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['83'])).
% 0.21/0.57  thf(dt_l1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.57  thf('85', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['84', '85'])).
% 0.21/0.57  thf('87', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57          | ~ (v1_tops_1 @ X16 @ X17)
% 0.21/0.57          | ((k2_pre_topc @ X17 @ X16) = (u1_struct_0 @ X17))
% 0.21/0.57          | ~ (l1_pre_topc @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '89'])).
% 0.21/0.57  thf('91', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['90'])).
% 0.21/0.57  thf('92', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['84', '85'])).
% 0.21/0.57  thf('93', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.57  thf('94', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.57          | ~ (v1_tops_1 @ X9 @ X10)
% 0.21/0.57          | ((k2_pre_topc @ X10 @ X9) = (k2_struct_0 @ X10))
% 0.21/0.57          | ~ (l1_pre_topc @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.21/0.57          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['92', '95'])).
% 0.21/0.57  thf('97', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['96'])).
% 0.21/0.57  thf('98', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['91', '97'])).
% 0.21/0.57  thf('99', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['98'])).
% 0.21/0.57  thf('100', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      ((((v1_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['99', '100'])).
% 0.21/0.57  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('103', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B_2 @ (k2_struct_0 @ sk_A)))
% 0.21/0.57         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.57  thf('104', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B_2 @ sk_B_2))
% 0.21/0.57         <= (((v3_tex_2 @ sk_B_2 @ sk_A)) & 
% 0.21/0.57             ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['71', '103'])).
% 0.21/0.57  thf('105', plain, (![X3 : $i]: ~ (v1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.21/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.57  thf('106', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.57  thf('107', plain, (![X3 : $i]: ~ (v1_subset_1 @ X3 @ X3)),
% 0.21/0.57      inference('demod', [status(thm)], ['105', '106'])).
% 0.21/0.57  thf('108', plain,
% 0.21/0.57      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 0.21/0.57       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['104', '107'])).
% 0.21/0.57  thf('109', plain,
% 0.21/0.57      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 0.21/0.57       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('110', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('111', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (((X19) = (X18))
% 0.21/0.57          | (v1_subset_1 @ X19 @ X18)
% 0.21/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.57  thf('112', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.57        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['110', '111'])).
% 0.21/0.57  thf('113', plain,
% 0.21/0.57      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('114', plain,
% 0.21/0.57      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.57  thf('115', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.57  thf(t48_tex_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.57             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('116', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.21/0.57          | (v3_tex_2 @ X29 @ X30)
% 0.21/0.57          | ~ (v2_tex_2 @ X29 @ X30)
% 0.21/0.57          | ~ (v1_tops_1 @ X29 @ X30)
% 0.21/0.57          | ~ (l1_pre_topc @ X30)
% 0.21/0.57          | ~ (v2_pre_topc @ X30)
% 0.21/0.57          | (v2_struct_0 @ X30))),
% 0.21/0.57      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.21/0.57  thf('117', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X0)
% 0.21/0.57          | ~ (v2_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.57          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.57          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['115', '116'])).
% 0.21/0.57  thf('118', plain,
% 0.21/0.57      (((~ (v1_tops_1 @ sk_B_2 @ sk_A)
% 0.21/0.57         | (v3_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57         | (v2_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['114', '117'])).
% 0.21/0.57  thf('119', plain,
% 0.21/0.57      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.57  thf('120', plain,
% 0.21/0.57      (![X7 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.57          | ~ (l1_struct_0 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.57  thf('121', plain,
% 0.21/0.57      ((((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.57         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['119', '120'])).
% 0.21/0.57  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('123', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.57  thf('124', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['122', '123'])).
% 0.21/0.57  thf('125', plain,
% 0.21/0.57      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_2)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['121', '124'])).
% 0.21/0.57  thf('126', plain,
% 0.21/0.57      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.57  thf('127', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.57          | ((k2_pre_topc @ X10 @ X9) != (k2_struct_0 @ X10))
% 0.21/0.57          | (v1_tops_1 @ X9 @ X10)
% 0.21/0.57          | ~ (l1_pre_topc @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.57  thf('128', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.57           | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57           | (v1_tops_1 @ X0 @ sk_A)
% 0.21/0.57           | ((k2_pre_topc @ sk_A @ X0) != (k2_struct_0 @ sk_A))))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['126', '127'])).
% 0.21/0.57  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('130', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.57           | (v1_tops_1 @ X0 @ sk_A)
% 0.21/0.57           | ((k2_pre_topc @ sk_A @ X0) != (k2_struct_0 @ sk_A))))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['128', '129'])).
% 0.21/0.57  thf('131', plain,
% 0.21/0.57      (((((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))
% 0.21/0.57         | (v1_tops_1 @ (k2_struct_0 @ sk_A) @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['125', '130'])).
% 0.21/0.57  thf('132', plain,
% 0.21/0.57      (![X11 : $i]:
% 0.21/0.57         ((v1_tops_1 @ (k2_struct_0 @ X11) @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc12_tops_1])).
% 0.21/0.57  thf('133', plain,
% 0.21/0.57      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_2)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['121', '124'])).
% 0.21/0.57  thf('134', plain,
% 0.21/0.57      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.57  thf('135', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.57          | ~ (v1_tops_1 @ X9 @ X10)
% 0.21/0.57          | ((k2_pre_topc @ X10 @ X9) = (k2_struct_0 @ X10))
% 0.21/0.57          | ~ (l1_pre_topc @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.57  thf('136', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.57           | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57           | ((k2_pre_topc @ sk_A @ X0) = (k2_struct_0 @ sk_A))
% 0.21/0.57           | ~ (v1_tops_1 @ X0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['134', '135'])).
% 0.21/0.57  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('138', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.57           | ((k2_pre_topc @ sk_A @ X0) = (k2_struct_0 @ sk_A))
% 0.21/0.57           | ~ (v1_tops_1 @ X0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['136', '137'])).
% 0.21/0.57  thf('139', plain,
% 0.21/0.57      (((~ (v1_tops_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57         | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['133', '138'])).
% 0.21/0.57  thf('140', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['132', '139'])).
% 0.21/0.57  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('142', plain,
% 0.21/0.57      ((((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['140', '141'])).
% 0.21/0.57  thf('143', plain,
% 0.21/0.57      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.21/0.57         | (v1_tops_1 @ (k2_struct_0 @ sk_A) @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['131', '142'])).
% 0.21/0.57  thf('144', plain,
% 0.21/0.57      (((v1_tops_1 @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['143'])).
% 0.21/0.57  thf('145', plain,
% 0.21/0.57      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_2)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['121', '124'])).
% 0.21/0.57  thf('146', plain,
% 0.21/0.57      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.57  thf('147', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.57          | ~ (v1_tops_1 @ X16 @ X17)
% 0.21/0.57          | ((k2_pre_topc @ X17 @ X16) = (u1_struct_0 @ X17))
% 0.21/0.57          | ~ (l1_pre_topc @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.57  thf('148', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.57           | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57           | ((k2_pre_topc @ sk_A @ X0) = (u1_struct_0 @ sk_A))
% 0.21/0.57           | ~ (v1_tops_1 @ X0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['146', '147'])).
% 0.21/0.57  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('150', plain,
% 0.21/0.57      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.57  thf('151', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_2))
% 0.21/0.57           | ((k2_pre_topc @ sk_A @ X0) = (sk_B_2))
% 0.21/0.57           | ~ (v1_tops_1 @ X0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.21/0.57  thf('152', plain,
% 0.21/0.57      (((~ (v1_tops_1 @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.57         | ((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (sk_B_2))))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['145', '151'])).
% 0.21/0.57  thf('153', plain,
% 0.21/0.57      (((v1_tops_1 @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['143'])).
% 0.21/0.57  thf('154', plain,
% 0.21/0.57      ((((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['140', '141'])).
% 0.21/0.57  thf('155', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (sk_B_2)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['152', '153', '154'])).
% 0.21/0.57  thf('156', plain,
% 0.21/0.57      (((v1_tops_1 @ sk_B_2 @ sk_A))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['144', '155'])).
% 0.21/0.57  thf('157', plain,
% 0.21/0.57      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.57  thf('158', plain,
% 0.21/0.57      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.57  thf('159', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('160', plain,
% 0.21/0.57      (![X25 : $i, X26 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.57          | (v2_tex_2 @ X25 @ X26)
% 0.21/0.57          | ~ (l1_pre_topc @ X26)
% 0.21/0.57          | ~ (v1_tdlat_3 @ X26)
% 0.21/0.57          | ~ (v2_pre_topc @ X26)
% 0.21/0.57          | (v2_struct_0 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.57  thf('161', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A)
% 0.21/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['159', '160'])).
% 0.21/0.57  thf('162', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('163', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('165', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 0.21/0.57  thf('166', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('167', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.21/0.57      inference('clc', [status(thm)], ['165', '166'])).
% 0.21/0.57  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('170', plain,
% 0.21/0.57      ((((v3_tex_2 @ sk_B_2 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)],
% 0.21/0.57                ['118', '156', '157', '158', '167', '168', '169'])).
% 0.21/0.57  thf('171', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('172', plain,
% 0.21/0.57      (((v3_tex_2 @ sk_B_2 @ sk_A))
% 0.21/0.57         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('clc', [status(thm)], ['170', '171'])).
% 0.21/0.57  thf('173', plain,
% 0.21/0.57      ((~ (v3_tex_2 @ sk_B_2 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('174', plain,
% 0.21/0.57      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 0.21/0.57       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['172', '173'])).
% 0.21/0.57  thf('175', plain, ($false),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['1', '108', '109', '174'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
