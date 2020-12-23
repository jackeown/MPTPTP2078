%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aVW5pjaRYX

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:51 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 443 expanded)
%              Number of leaves         :   42 ( 143 expanded)
%              Depth                    :   18
%              Number of atoms          :  908 (4406 expanded)
%              Number of equality atoms :   41 (  89 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v1_tdlat_3 @ X37 )
      | ( v2_tex_2 @ X36 @ X37 )
      | ( X36
       != ( u1_struct_0 @ X37 ) )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('2',plain,(
    ! [X37: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X37 ) @ X37 )
      | ~ ( v1_tdlat_3 @ X37 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X37: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X37 ) @ X37 )
      | ~ ( v1_tdlat_3 @ X37 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t29_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_tex_2 @ B @ A )
                  | ( v2_tex_2 @ C @ A ) )
               => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v2_tex_2 @ X38 @ X39 )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_tex_2])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['11','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X27 @ X26 ) )
        = X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('40',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('46',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('49',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( X35
       != ( u1_struct_0 @ X33 ) )
      | ~ ( v1_tdlat_3 @ X33 )
      | ( v2_tex_2 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('59',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X33 ) @ X34 )
      | ~ ( v1_tdlat_3 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf(cc5_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_borsuk_1 @ B @ A )
            & ( v1_tsep_1 @ B @ A )
            & ( v1_tdlat_3 @ B ) ) ) ) )).

thf('62',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( v1_tdlat_3 @ X31 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_tdlat_3 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v2_tex_2 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','79'])).

thf('81',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','81'])).

thf('83',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','82'])).

thf('84',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf('87',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('92',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','79'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['83','84','85','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aVW5pjaRYX
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.67/2.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.67/2.89  % Solved by: fo/fo7.sh
% 2.67/2.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.67/2.89  % done 3059 iterations in 2.434s
% 2.67/2.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.67/2.89  % SZS output start Refutation
% 2.67/2.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.67/2.89  thf(sk_A_type, type, sk_A: $i).
% 2.67/2.89  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 2.67/2.89  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 2.67/2.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.67/2.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.67/2.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.67/2.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.67/2.89  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.67/2.89  thf(sk_B_type, type, sk_B: $i).
% 2.67/2.89  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 2.67/2.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.67/2.89  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 2.67/2.89  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 2.67/2.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.67/2.89  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.67/2.89  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.67/2.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.67/2.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.67/2.89  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.67/2.89  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 2.67/2.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.67/2.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.67/2.89  thf(t43_tex_2, conjecture,
% 2.67/2.89    (![A:$i]:
% 2.67/2.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 2.67/2.89         ( l1_pre_topc @ A ) ) =>
% 2.67/2.89       ( ![B:$i]:
% 2.67/2.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.89           ( v2_tex_2 @ B @ A ) ) ) ))).
% 2.67/2.89  thf(zf_stmt_0, negated_conjecture,
% 2.67/2.89    (~( ![A:$i]:
% 2.67/2.89        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.67/2.89            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.67/2.89          ( ![B:$i]:
% 2.67/2.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.89              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 2.67/2.89    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 2.67/2.89  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf(t27_tex_2, axiom,
% 2.67/2.89    (![A:$i]:
% 2.67/2.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 2.67/2.89       ( ![B:$i]:
% 2.67/2.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.89           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 2.67/2.89             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 2.67/2.89  thf('1', plain,
% 2.67/2.89      (![X36 : $i, X37 : $i]:
% 2.67/2.89         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.67/2.89          | ~ (v1_tdlat_3 @ X37)
% 2.67/2.89          | (v2_tex_2 @ X36 @ X37)
% 2.67/2.89          | ((X36) != (u1_struct_0 @ X37))
% 2.67/2.89          | ~ (l1_pre_topc @ X37)
% 2.67/2.89          | (v2_struct_0 @ X37))),
% 2.67/2.89      inference('cnf', [status(esa)], [t27_tex_2])).
% 2.67/2.89  thf('2', plain,
% 2.67/2.89      (![X37 : $i]:
% 2.67/2.89         ((v2_struct_0 @ X37)
% 2.67/2.89          | ~ (l1_pre_topc @ X37)
% 2.67/2.89          | (v2_tex_2 @ (u1_struct_0 @ X37) @ X37)
% 2.67/2.89          | ~ (v1_tdlat_3 @ X37)
% 2.67/2.89          | ~ (m1_subset_1 @ (u1_struct_0 @ X37) @ 
% 2.67/2.89               (k1_zfmisc_1 @ (u1_struct_0 @ X37))))),
% 2.67/2.89      inference('simplify', [status(thm)], ['1'])).
% 2.67/2.89  thf(dt_k2_subset_1, axiom,
% 2.67/2.89    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.67/2.89  thf('3', plain,
% 2.67/2.89      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 2.67/2.89      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 2.67/2.89  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.67/2.89  thf('4', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 2.67/2.89      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.67/2.89  thf('5', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 2.67/2.89      inference('demod', [status(thm)], ['3', '4'])).
% 2.67/2.89  thf('6', plain,
% 2.67/2.89      (![X37 : $i]:
% 2.67/2.89         ((v2_struct_0 @ X37)
% 2.67/2.89          | ~ (l1_pre_topc @ X37)
% 2.67/2.89          | (v2_tex_2 @ (u1_struct_0 @ X37) @ X37)
% 2.67/2.89          | ~ (v1_tdlat_3 @ X37))),
% 2.67/2.89      inference('demod', [status(thm)], ['2', '5'])).
% 2.67/2.89  thf(t4_subset_1, axiom,
% 2.67/2.89    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.67/2.89  thf('7', plain,
% 2.67/2.89      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 2.67/2.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.67/2.89  thf('8', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 2.67/2.89      inference('demod', [status(thm)], ['3', '4'])).
% 2.67/2.89  thf(t29_tex_2, axiom,
% 2.67/2.89    (![A:$i]:
% 2.67/2.89     ( ( l1_pre_topc @ A ) =>
% 2.67/2.89       ( ![B:$i]:
% 2.67/2.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.89           ( ![C:$i]:
% 2.67/2.89             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.89               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 2.67/2.89                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 2.67/2.89  thf('9', plain,
% 2.67/2.89      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.67/2.89         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 2.67/2.89          | ~ (v2_tex_2 @ X38 @ X39)
% 2.67/2.89          | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ X39) @ X38 @ X40) @ X39)
% 2.67/2.89          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 2.67/2.89          | ~ (l1_pre_topc @ X39))),
% 2.67/2.89      inference('cnf', [status(esa)], [t29_tex_2])).
% 2.67/2.89  thf('10', plain,
% 2.67/2.89      (![X0 : $i, X1 : $i]:
% 2.67/2.89         (~ (l1_pre_topc @ X0)
% 2.67/2.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.67/2.89          | (v2_tex_2 @ 
% 2.67/2.89             (k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ X0)
% 2.67/2.89          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['8', '9'])).
% 2.67/2.89  thf('11', plain,
% 2.67/2.89      (![X0 : $i]:
% 2.67/2.89         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 2.67/2.89          | (v2_tex_2 @ 
% 2.67/2.89             (k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 2.67/2.89              k1_xboole_0) @ 
% 2.67/2.89             X0)
% 2.67/2.89          | ~ (l1_pre_topc @ X0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['7', '10'])).
% 2.67/2.89  thf('12', plain,
% 2.67/2.89      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 2.67/2.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.67/2.89  thf(redefinition_k9_subset_1, axiom,
% 2.67/2.89    (![A:$i,B:$i,C:$i]:
% 2.67/2.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.89       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 2.67/2.89  thf('13', plain,
% 2.67/2.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.67/2.89         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 2.67/2.89          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 2.67/2.89      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.67/2.89  thf('14', plain,
% 2.67/2.89      (![X0 : $i, X1 : $i]:
% 2.67/2.89         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 2.67/2.89           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['12', '13'])).
% 2.67/2.89  thf(d10_xboole_0, axiom,
% 2.67/2.89    (![A:$i,B:$i]:
% 2.67/2.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.67/2.89  thf('15', plain,
% 2.67/2.89      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 2.67/2.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.67/2.89  thf('16', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 2.67/2.89      inference('simplify', [status(thm)], ['15'])).
% 2.67/2.89  thf(l32_xboole_1, axiom,
% 2.67/2.89    (![A:$i,B:$i]:
% 2.67/2.89     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.67/2.89  thf('17', plain,
% 2.67/2.89      (![X4 : $i, X6 : $i]:
% 2.67/2.89         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 2.67/2.89      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.67/2.89  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['16', '17'])).
% 2.67/2.89  thf(t48_xboole_1, axiom,
% 2.67/2.89    (![A:$i,B:$i]:
% 2.67/2.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.67/2.89  thf('19', plain,
% 2.67/2.89      (![X9 : $i, X10 : $i]:
% 2.67/2.89         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 2.67/2.89           = (k3_xboole_0 @ X9 @ X10))),
% 2.67/2.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.89  thf('20', plain,
% 2.67/2.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.67/2.89      inference('sup+', [status(thm)], ['18', '19'])).
% 2.67/2.89  thf('21', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 2.67/2.89      inference('simplify', [status(thm)], ['15'])).
% 2.67/2.89  thf(t28_xboole_1, axiom,
% 2.67/2.89    (![A:$i,B:$i]:
% 2.67/2.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.67/2.89  thf('22', plain,
% 2.67/2.89      (![X7 : $i, X8 : $i]:
% 2.67/2.89         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 2.67/2.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.67/2.89  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['21', '22'])).
% 2.67/2.89  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.67/2.89      inference('demod', [status(thm)], ['20', '23'])).
% 2.67/2.89  thf('25', plain,
% 2.67/2.89      (![X9 : $i, X10 : $i]:
% 2.67/2.89         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 2.67/2.89           = (k3_xboole_0 @ X9 @ X10))),
% 2.67/2.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.89  thf('26', plain,
% 2.67/2.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.67/2.89      inference('sup+', [status(thm)], ['24', '25'])).
% 2.67/2.89  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['16', '17'])).
% 2.67/2.89  thf('28', plain,
% 2.67/2.89      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.67/2.89      inference('demod', [status(thm)], ['26', '27'])).
% 2.67/2.89  thf('29', plain,
% 2.67/2.89      (![X0 : $i, X1 : $i]:
% 2.67/2.89         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.67/2.89      inference('demod', [status(thm)], ['14', '28'])).
% 2.67/2.89  thf('30', plain,
% 2.67/2.89      (![X0 : $i]:
% 2.67/2.89         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 2.67/2.89          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 2.67/2.89          | ~ (l1_pre_topc @ X0))),
% 2.67/2.89      inference('demod', [status(thm)], ['11', '29'])).
% 2.67/2.89  thf('31', plain,
% 2.67/2.89      (![X0 : $i]:
% 2.67/2.89         (~ (v1_tdlat_3 @ X0)
% 2.67/2.89          | ~ (l1_pre_topc @ X0)
% 2.67/2.89          | (v2_struct_0 @ X0)
% 2.67/2.89          | ~ (l1_pre_topc @ X0)
% 2.67/2.89          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['6', '30'])).
% 2.67/2.89  thf('32', plain,
% 2.67/2.89      (![X0 : $i]:
% 2.67/2.89         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 2.67/2.89          | (v2_struct_0 @ X0)
% 2.67/2.89          | ~ (l1_pre_topc @ X0)
% 2.67/2.89          | ~ (v1_tdlat_3 @ X0))),
% 2.67/2.89      inference('simplify', [status(thm)], ['31'])).
% 2.67/2.89  thf(l13_xboole_0, axiom,
% 2.67/2.89    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.67/2.89  thf('33', plain,
% 2.67/2.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.67/2.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.67/2.89  thf('34', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('35', plain,
% 2.67/2.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf(t29_pre_topc, axiom,
% 2.67/2.89    (![A:$i]:
% 2.67/2.89     ( ( l1_pre_topc @ A ) =>
% 2.67/2.89       ( ![B:$i]:
% 2.67/2.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.89           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 2.67/2.89  thf('36', plain,
% 2.67/2.89      (![X26 : $i, X27 : $i]:
% 2.67/2.89         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 2.67/2.89          | ((u1_struct_0 @ (k1_pre_topc @ X27 @ X26)) = (X26))
% 2.67/2.89          | ~ (l1_pre_topc @ X27))),
% 2.67/2.89      inference('cnf', [status(esa)], [t29_pre_topc])).
% 2.67/2.89  thf('37', plain,
% 2.67/2.89      ((~ (l1_pre_topc @ sk_A)
% 2.67/2.89        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 2.67/2.89      inference('sup-', [status(thm)], ['35', '36'])).
% 2.67/2.89  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('39', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.67/2.89      inference('demod', [status(thm)], ['37', '38'])).
% 2.67/2.89  thf(fc1_struct_0, axiom,
% 2.67/2.89    (![A:$i]:
% 2.67/2.89     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 2.67/2.89       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 2.67/2.89  thf('40', plain,
% 2.67/2.89      (![X25 : $i]:
% 2.67/2.89         ((v1_xboole_0 @ (u1_struct_0 @ X25))
% 2.67/2.89          | ~ (l1_struct_0 @ X25)
% 2.67/2.89          | ~ (v2_struct_0 @ X25))),
% 2.67/2.89      inference('cnf', [status(esa)], [fc1_struct_0])).
% 2.67/2.89  thf('41', plain,
% 2.67/2.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.67/2.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.67/2.89  thf('42', plain,
% 2.67/2.89      (![X0 : $i]:
% 2.67/2.89         (~ (v2_struct_0 @ X0)
% 2.67/2.89          | ~ (l1_struct_0 @ X0)
% 2.67/2.89          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 2.67/2.89      inference('sup-', [status(thm)], ['40', '41'])).
% 2.67/2.89  thf('43', plain,
% 2.67/2.89      ((((sk_B) = (k1_xboole_0))
% 2.67/2.89        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.67/2.89        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.67/2.89      inference('sup+', [status(thm)], ['39', '42'])).
% 2.67/2.89  thf('44', plain,
% 2.67/2.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf(dt_k1_pre_topc, axiom,
% 2.67/2.89    (![A:$i,B:$i]:
% 2.67/2.89     ( ( ( l1_pre_topc @ A ) & 
% 2.67/2.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.67/2.89       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 2.67/2.89         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 2.67/2.89  thf('45', plain,
% 2.67/2.89      (![X20 : $i, X21 : $i]:
% 2.67/2.89         (~ (l1_pre_topc @ X20)
% 2.67/2.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.67/2.89          | (m1_pre_topc @ (k1_pre_topc @ X20 @ X21) @ X20))),
% 2.67/2.89      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 2.67/2.89  thf('46', plain,
% 2.67/2.89      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.67/2.89        | ~ (l1_pre_topc @ sk_A))),
% 2.67/2.89      inference('sup-', [status(thm)], ['44', '45'])).
% 2.67/2.89  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('48', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.67/2.89      inference('demod', [status(thm)], ['46', '47'])).
% 2.67/2.89  thf(dt_m1_pre_topc, axiom,
% 2.67/2.89    (![A:$i]:
% 2.67/2.89     ( ( l1_pre_topc @ A ) =>
% 2.67/2.89       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 2.67/2.89  thf('49', plain,
% 2.67/2.89      (![X23 : $i, X24 : $i]:
% 2.67/2.89         (~ (m1_pre_topc @ X23 @ X24)
% 2.67/2.89          | (l1_pre_topc @ X23)
% 2.67/2.89          | ~ (l1_pre_topc @ X24))),
% 2.67/2.89      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 2.67/2.89  thf('50', plain,
% 2.67/2.89      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.67/2.89      inference('sup-', [status(thm)], ['48', '49'])).
% 2.67/2.89  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('52', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.67/2.89      inference('demod', [status(thm)], ['50', '51'])).
% 2.67/2.89  thf(dt_l1_pre_topc, axiom,
% 2.67/2.89    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.67/2.89  thf('53', plain,
% 2.67/2.89      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 2.67/2.89      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.67/2.89  thf('54', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.67/2.89      inference('sup-', [status(thm)], ['52', '53'])).
% 2.67/2.89  thf('55', plain,
% 2.67/2.89      ((((sk_B) = (k1_xboole_0))
% 2.67/2.89        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.67/2.89      inference('demod', [status(thm)], ['43', '54'])).
% 2.67/2.89  thf('56', plain,
% 2.67/2.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('57', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.67/2.89      inference('demod', [status(thm)], ['37', '38'])).
% 2.67/2.89  thf(t26_tex_2, axiom,
% 2.67/2.89    (![A:$i]:
% 2.67/2.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 2.67/2.89       ( ![B:$i]:
% 2.67/2.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.67/2.89           ( ![C:$i]:
% 2.67/2.89             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.89               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 2.67/2.89                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 2.67/2.89  thf('58', plain,
% 2.67/2.89      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.67/2.89         ((v2_struct_0 @ X33)
% 2.67/2.89          | ~ (m1_pre_topc @ X33 @ X34)
% 2.67/2.89          | ((X35) != (u1_struct_0 @ X33))
% 2.67/2.89          | ~ (v1_tdlat_3 @ X33)
% 2.67/2.89          | (v2_tex_2 @ X35 @ X34)
% 2.67/2.89          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.67/2.89          | ~ (l1_pre_topc @ X34)
% 2.67/2.89          | (v2_struct_0 @ X34))),
% 2.67/2.89      inference('cnf', [status(esa)], [t26_tex_2])).
% 2.67/2.89  thf('59', plain,
% 2.67/2.89      (![X33 : $i, X34 : $i]:
% 2.67/2.89         ((v2_struct_0 @ X34)
% 2.67/2.89          | ~ (l1_pre_topc @ X34)
% 2.67/2.89          | ~ (m1_subset_1 @ (u1_struct_0 @ X33) @ 
% 2.67/2.89               (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.67/2.89          | (v2_tex_2 @ (u1_struct_0 @ X33) @ X34)
% 2.67/2.89          | ~ (v1_tdlat_3 @ X33)
% 2.67/2.89          | ~ (m1_pre_topc @ X33 @ X34)
% 2.67/2.89          | (v2_struct_0 @ X33))),
% 2.67/2.89      inference('simplify', [status(thm)], ['58'])).
% 2.67/2.89  thf('60', plain,
% 2.67/2.89      (![X0 : $i]:
% 2.67/2.89         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.67/2.89          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.67/2.89          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 2.67/2.89          | ~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.67/2.89          | (v2_tex_2 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ X0)
% 2.67/2.89          | ~ (l1_pre_topc @ X0)
% 2.67/2.89          | (v2_struct_0 @ X0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['57', '59'])).
% 2.67/2.89  thf('61', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.67/2.89      inference('demod', [status(thm)], ['46', '47'])).
% 2.67/2.89  thf(cc5_tdlat_3, axiom,
% 2.67/2.89    (![A:$i]:
% 2.67/2.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 2.67/2.89         ( l1_pre_topc @ A ) ) =>
% 2.67/2.89       ( ![B:$i]:
% 2.67/2.89         ( ( m1_pre_topc @ B @ A ) =>
% 2.67/2.89           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 2.67/2.89             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 2.67/2.89  thf('62', plain,
% 2.67/2.89      (![X31 : $i, X32 : $i]:
% 2.67/2.89         (~ (m1_pre_topc @ X31 @ X32)
% 2.67/2.89          | (v1_tdlat_3 @ X31)
% 2.67/2.89          | ~ (l1_pre_topc @ X32)
% 2.67/2.89          | ~ (v1_tdlat_3 @ X32)
% 2.67/2.89          | ~ (v2_pre_topc @ X32)
% 2.67/2.89          | (v2_struct_0 @ X32))),
% 2.67/2.89      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 2.67/2.89  thf('63', plain,
% 2.67/2.89      (((v2_struct_0 @ sk_A)
% 2.67/2.89        | ~ (v2_pre_topc @ sk_A)
% 2.67/2.89        | ~ (v1_tdlat_3 @ sk_A)
% 2.67/2.89        | ~ (l1_pre_topc @ sk_A)
% 2.67/2.89        | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.67/2.89      inference('sup-', [status(thm)], ['61', '62'])).
% 2.67/2.89  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('65', plain, ((v1_tdlat_3 @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('67', plain,
% 2.67/2.89      (((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.67/2.89      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 2.67/2.89  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('69', plain, ((v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.67/2.89      inference('clc', [status(thm)], ['67', '68'])).
% 2.67/2.89  thf('70', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.67/2.89      inference('demod', [status(thm)], ['37', '38'])).
% 2.67/2.89  thf('71', plain,
% 2.67/2.89      (![X0 : $i]:
% 2.67/2.89         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.67/2.89          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.67/2.89          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 2.67/2.89          | (v2_tex_2 @ sk_B @ X0)
% 2.67/2.89          | ~ (l1_pre_topc @ X0)
% 2.67/2.89          | (v2_struct_0 @ X0))),
% 2.67/2.89      inference('demod', [status(thm)], ['60', '69', '70'])).
% 2.67/2.89  thf('72', plain,
% 2.67/2.89      (((v2_struct_0 @ sk_A)
% 2.67/2.89        | ~ (l1_pre_topc @ sk_A)
% 2.67/2.89        | (v2_tex_2 @ sk_B @ sk_A)
% 2.67/2.89        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.67/2.89        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.67/2.89      inference('sup-', [status(thm)], ['56', '71'])).
% 2.67/2.89  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('74', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.67/2.89      inference('demod', [status(thm)], ['46', '47'])).
% 2.67/2.89  thf('75', plain,
% 2.67/2.89      (((v2_struct_0 @ sk_A)
% 2.67/2.89        | (v2_tex_2 @ sk_B @ sk_A)
% 2.67/2.89        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.67/2.89      inference('demod', [status(thm)], ['72', '73', '74'])).
% 2.67/2.89  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('77', plain,
% 2.67/2.89      (((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) | (v2_tex_2 @ sk_B @ sk_A))),
% 2.67/2.89      inference('clc', [status(thm)], ['75', '76'])).
% 2.67/2.89  thf('78', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('79', plain, ((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.67/2.89      inference('clc', [status(thm)], ['77', '78'])).
% 2.67/2.89  thf('80', plain, (((sk_B) = (k1_xboole_0))),
% 2.67/2.89      inference('demod', [status(thm)], ['55', '79'])).
% 2.67/2.89  thf('81', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 2.67/2.89      inference('demod', [status(thm)], ['34', '80'])).
% 2.67/2.89  thf('82', plain,
% 2.67/2.89      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['33', '81'])).
% 2.67/2.89  thf('83', plain,
% 2.67/2.89      ((~ (v1_tdlat_3 @ sk_A)
% 2.67/2.89        | ~ (l1_pre_topc @ sk_A)
% 2.67/2.89        | (v2_struct_0 @ sk_A)
% 2.67/2.89        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.67/2.89      inference('sup-', [status(thm)], ['32', '82'])).
% 2.67/2.89  thf('84', plain, ((v1_tdlat_3 @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.89  thf('86', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.67/2.89      inference('demod', [status(thm)], ['37', '38'])).
% 2.67/2.89  thf('87', plain,
% 2.67/2.89      (![X25 : $i]:
% 2.67/2.89         ((v1_xboole_0 @ (u1_struct_0 @ X25))
% 2.67/2.89          | ~ (l1_struct_0 @ X25)
% 2.67/2.89          | ~ (v2_struct_0 @ X25))),
% 2.67/2.89      inference('cnf', [status(esa)], [fc1_struct_0])).
% 2.67/2.89  thf('88', plain,
% 2.67/2.89      (((v1_xboole_0 @ sk_B)
% 2.67/2.89        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.67/2.89        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.67/2.89      inference('sup+', [status(thm)], ['86', '87'])).
% 2.67/2.89  thf('89', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.67/2.89      inference('sup-', [status(thm)], ['52', '53'])).
% 2.67/2.89  thf('90', plain,
% 2.67/2.89      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.67/2.89      inference('demod', [status(thm)], ['88', '89'])).
% 2.67/2.89  thf('91', plain, ((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.67/2.89      inference('clc', [status(thm)], ['77', '78'])).
% 2.67/2.89  thf('92', plain, ((v1_xboole_0 @ sk_B)),
% 2.67/2.89      inference('demod', [status(thm)], ['90', '91'])).
% 2.67/2.89  thf('93', plain, (((sk_B) = (k1_xboole_0))),
% 2.67/2.89      inference('demod', [status(thm)], ['55', '79'])).
% 2.67/2.89  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.67/2.89      inference('demod', [status(thm)], ['92', '93'])).
% 2.67/2.89  thf('95', plain, ((v2_struct_0 @ sk_A)),
% 2.67/2.89      inference('demod', [status(thm)], ['83', '84', '85', '94'])).
% 2.73/2.89  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 2.73/2.89  
% 2.73/2.89  % SZS output end Refutation
% 2.73/2.89  
% 2.73/2.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
