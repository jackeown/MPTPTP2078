%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BvRTd98eKG

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:51 EST 2020

% Result     : Theorem 3.02s
% Output     : Refutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  180 (1231 expanded)
%              Number of leaves         :   39 ( 355 expanded)
%              Depth                    :   29
%              Number of atoms          : 1335 (13640 expanded)
%              Number of equality atoms :   33 ( 169 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v1_tdlat_3 @ X36 )
      | ( v2_tex_2 @ X35 @ X36 )
      | ( X35
       != ( u1_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('2',plain,(
    ! [X36: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X36 ) @ X36 )
      | ~ ( v1_tdlat_3 @ X36 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X36: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X36 ) @ X36 )
      | ~ ( v1_tdlat_3 @ X36 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( X30
        = ( u1_struct_0 @ ( sk_C_1 @ X30 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X30 @ X31 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

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

thf('34',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v1_tdlat_3 @ X28 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v1_tdlat_3 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( X34
       != ( u1_struct_0 @ X32 ) )
      | ~ ( v1_tdlat_3 @ X32 )
      | ( v2_tex_2 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('49',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X32 ) @ X33 )
      | ~ ( v1_tdlat_3 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X30 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['19','71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('75',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tops_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k1_tops_1 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup+',[status(thm)],['72','86'])).

thf('88',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
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

thf('92',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tex_2 @ X37 @ X38 )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t29_tex_2])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('96',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('97',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('100',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_subset_1 @ X0 @ X1 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['95','106'])).

thf('108',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('110',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k9_subset_1 @ X0 @ X3 @ ( k3_xboole_0 @ X2 @ X1 ) )
        = ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X2 @ X1 @ sk_B )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['95','106'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['95','106'])).

thf('122',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('123',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X2 @ X1 @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_tex_2 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['94','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ sk_B @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('138',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['0','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BvRTd98eKG
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.02/3.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.02/3.20  % Solved by: fo/fo7.sh
% 3.02/3.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.02/3.20  % done 4562 iterations in 2.745s
% 3.02/3.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.02/3.20  % SZS output start Refutation
% 3.02/3.20  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.02/3.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.02/3.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.02/3.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.02/3.20  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.02/3.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.02/3.20  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 3.02/3.20  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 3.02/3.20  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.02/3.20  thf(sk_A_type, type, sk_A: $i).
% 3.02/3.20  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.02/3.20  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 3.02/3.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.02/3.20  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 3.02/3.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.02/3.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.02/3.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.02/3.20  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 3.02/3.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.02/3.20  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 3.02/3.20  thf(sk_B_type, type, sk_B: $i).
% 3.02/3.20  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.02/3.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.02/3.20  thf(t43_tex_2, conjecture,
% 3.02/3.20    (![A:$i]:
% 3.02/3.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 3.02/3.20         ( l1_pre_topc @ A ) ) =>
% 3.02/3.20       ( ![B:$i]:
% 3.02/3.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.02/3.20           ( v2_tex_2 @ B @ A ) ) ) ))).
% 3.02/3.20  thf(zf_stmt_0, negated_conjecture,
% 3.02/3.20    (~( ![A:$i]:
% 3.02/3.20        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.02/3.20            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.02/3.20          ( ![B:$i]:
% 3.02/3.20            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.02/3.20              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 3.02/3.20    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 3.02/3.20  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 3.02/3.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.20  thf(t27_tex_2, axiom,
% 3.02/3.20    (![A:$i]:
% 3.02/3.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 3.02/3.20       ( ![B:$i]:
% 3.02/3.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.02/3.20           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 3.02/3.20             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 3.02/3.20  thf('1', plain,
% 3.02/3.20      (![X35 : $i, X36 : $i]:
% 3.02/3.20         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 3.02/3.20          | ~ (v1_tdlat_3 @ X36)
% 3.02/3.20          | (v2_tex_2 @ X35 @ X36)
% 3.02/3.20          | ((X35) != (u1_struct_0 @ X36))
% 3.02/3.20          | ~ (l1_pre_topc @ X36)
% 3.02/3.20          | (v2_struct_0 @ X36))),
% 3.02/3.20      inference('cnf', [status(esa)], [t27_tex_2])).
% 3.02/3.20  thf('2', plain,
% 3.02/3.20      (![X36 : $i]:
% 3.02/3.20         ((v2_struct_0 @ X36)
% 3.02/3.20          | ~ (l1_pre_topc @ X36)
% 3.02/3.20          | (v2_tex_2 @ (u1_struct_0 @ X36) @ X36)
% 3.02/3.20          | ~ (v1_tdlat_3 @ X36)
% 3.02/3.20          | ~ (m1_subset_1 @ (u1_struct_0 @ X36) @ 
% 3.02/3.20               (k1_zfmisc_1 @ (u1_struct_0 @ X36))))),
% 3.02/3.21      inference('simplify', [status(thm)], ['1'])).
% 3.02/3.21  thf(dt_k2_subset_1, axiom,
% 3.02/3.21    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.02/3.21  thf('3', plain,
% 3.02/3.21      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 3.02/3.21      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 3.02/3.21  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.02/3.21  thf('4', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 3.02/3.21      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.02/3.21  thf('5', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 3.02/3.21      inference('demod', [status(thm)], ['3', '4'])).
% 3.02/3.21  thf('6', plain,
% 3.02/3.21      (![X36 : $i]:
% 3.02/3.21         ((v2_struct_0 @ X36)
% 3.02/3.21          | ~ (l1_pre_topc @ X36)
% 3.02/3.21          | (v2_tex_2 @ (u1_struct_0 @ X36) @ X36)
% 3.02/3.21          | ~ (v1_tdlat_3 @ X36))),
% 3.02/3.21      inference('demod', [status(thm)], ['2', '5'])).
% 3.02/3.21  thf('7', plain,
% 3.02/3.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf(t44_tops_1, axiom,
% 3.02/3.21    (![A:$i]:
% 3.02/3.21     ( ( l1_pre_topc @ A ) =>
% 3.02/3.21       ( ![B:$i]:
% 3.02/3.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.02/3.21           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 3.02/3.21  thf('8', plain,
% 3.02/3.21      (![X23 : $i, X24 : $i]:
% 3.02/3.21         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 3.02/3.21          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ X23)
% 3.02/3.21          | ~ (l1_pre_topc @ X24))),
% 3.02/3.21      inference('cnf', [status(esa)], [t44_tops_1])).
% 3.02/3.21  thf('9', plain,
% 3.02/3.21      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['7', '8'])).
% 3.02/3.21  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('11', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 3.02/3.21      inference('demod', [status(thm)], ['9', '10'])).
% 3.02/3.21  thf(d3_tarski, axiom,
% 3.02/3.21    (![A:$i,B:$i]:
% 3.02/3.21     ( ( r1_tarski @ A @ B ) <=>
% 3.02/3.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.02/3.21  thf('12', plain,
% 3.02/3.21      (![X1 : $i, X3 : $i]:
% 3.02/3.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.02/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.02/3.21  thf('13', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 3.02/3.21      inference('demod', [status(thm)], ['3', '4'])).
% 3.02/3.21  thf(t5_subset, axiom,
% 3.02/3.21    (![A:$i,B:$i,C:$i]:
% 3.02/3.21     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.02/3.21          ( v1_xboole_0 @ C ) ) ))).
% 3.02/3.21  thf('14', plain,
% 3.02/3.21      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X20 @ X21)
% 3.02/3.21          | ~ (v1_xboole_0 @ X22)
% 3.02/3.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 3.02/3.21      inference('cnf', [status(esa)], [t5_subset])).
% 3.02/3.21  thf('15', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['13', '14'])).
% 3.02/3.21  thf('16', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['12', '15'])).
% 3.02/3.21  thf(d10_xboole_0, axiom,
% 3.02/3.21    (![A:$i,B:$i]:
% 3.02/3.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.02/3.21  thf('17', plain,
% 3.02/3.21      (![X4 : $i, X6 : $i]:
% 3.02/3.21         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.02/3.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.02/3.21  thf('18', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['16', '17'])).
% 3.02/3.21  thf('19', plain,
% 3.02/3.21      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['11', '18'])).
% 3.02/3.21  thf('20', plain,
% 3.02/3.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf(t10_tsep_1, axiom,
% 3.02/3.21    (![A:$i]:
% 3.02/3.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 3.02/3.21       ( ![B:$i]:
% 3.02/3.21         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 3.02/3.21             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.02/3.21           ( ?[C:$i]:
% 3.02/3.21             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 3.02/3.21               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 3.02/3.21  thf('21', plain,
% 3.02/3.21      (![X30 : $i, X31 : $i]:
% 3.02/3.21         ((v1_xboole_0 @ X30)
% 3.02/3.21          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 3.02/3.21          | ((X30) = (u1_struct_0 @ (sk_C_1 @ X30 @ X31)))
% 3.02/3.21          | ~ (l1_pre_topc @ X31)
% 3.02/3.21          | (v2_struct_0 @ X31))),
% 3.02/3.21      inference('cnf', [status(esa)], [t10_tsep_1])).
% 3.02/3.21  thf('22', plain,
% 3.02/3.21      (((v2_struct_0 @ sk_A)
% 3.02/3.21        | ~ (l1_pre_topc @ sk_A)
% 3.02/3.21        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['20', '21'])).
% 3.02/3.21  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('24', plain,
% 3.02/3.21      (((v2_struct_0 @ sk_A)
% 3.02/3.21        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('demod', [status(thm)], ['22', '23'])).
% 3.02/3.21  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('26', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B)
% 3.02/3.21        | ((sk_B) = (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A))))),
% 3.02/3.21      inference('clc', [status(thm)], ['24', '25'])).
% 3.02/3.21  thf('27', plain,
% 3.02/3.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('28', plain,
% 3.02/3.21      (![X30 : $i, X31 : $i]:
% 3.02/3.21         ((v1_xboole_0 @ X30)
% 3.02/3.21          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 3.02/3.21          | (m1_pre_topc @ (sk_C_1 @ X30 @ X31) @ X31)
% 3.02/3.21          | ~ (l1_pre_topc @ X31)
% 3.02/3.21          | (v2_struct_0 @ X31))),
% 3.02/3.21      inference('cnf', [status(esa)], [t10_tsep_1])).
% 3.02/3.21  thf('29', plain,
% 3.02/3.21      (((v2_struct_0 @ sk_A)
% 3.02/3.21        | ~ (l1_pre_topc @ sk_A)
% 3.02/3.21        | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['27', '28'])).
% 3.02/3.21  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('31', plain,
% 3.02/3.21      (((v2_struct_0 @ sk_A)
% 3.02/3.21        | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('demod', [status(thm)], ['29', '30'])).
% 3.02/3.21  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('33', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 3.02/3.21      inference('clc', [status(thm)], ['31', '32'])).
% 3.02/3.21  thf(cc5_tdlat_3, axiom,
% 3.02/3.21    (![A:$i]:
% 3.02/3.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 3.02/3.21         ( l1_pre_topc @ A ) ) =>
% 3.02/3.21       ( ![B:$i]:
% 3.02/3.21         ( ( m1_pre_topc @ B @ A ) =>
% 3.02/3.21           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 3.02/3.21             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 3.02/3.21  thf('34', plain,
% 3.02/3.21      (![X28 : $i, X29 : $i]:
% 3.02/3.21         (~ (m1_pre_topc @ X28 @ X29)
% 3.02/3.21          | (v1_tdlat_3 @ X28)
% 3.02/3.21          | ~ (l1_pre_topc @ X29)
% 3.02/3.21          | ~ (v1_tdlat_3 @ X29)
% 3.02/3.21          | ~ (v2_pre_topc @ X29)
% 3.02/3.21          | (v2_struct_0 @ X29))),
% 3.02/3.21      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 3.02/3.21  thf('35', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | ~ (v2_pre_topc @ sk_A)
% 3.02/3.21        | ~ (v1_tdlat_3 @ sk_A)
% 3.02/3.21        | ~ (l1_pre_topc @ sk_A)
% 3.02/3.21        | (v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['33', '34'])).
% 3.02/3.21  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('37', plain, ((v1_tdlat_3 @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('39', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | (v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A)))),
% 3.02/3.21      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 3.02/3.21  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('41', plain,
% 3.02/3.21      (((v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('clc', [status(thm)], ['39', '40'])).
% 3.02/3.21  thf('42', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 3.02/3.21      inference('clc', [status(thm)], ['31', '32'])).
% 3.02/3.21  thf('43', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B) | (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A))),
% 3.02/3.21      inference('clc', [status(thm)], ['31', '32'])).
% 3.02/3.21  thf(t1_tsep_1, axiom,
% 3.02/3.21    (![A:$i]:
% 3.02/3.21     ( ( l1_pre_topc @ A ) =>
% 3.02/3.21       ( ![B:$i]:
% 3.02/3.21         ( ( m1_pre_topc @ B @ A ) =>
% 3.02/3.21           ( m1_subset_1 @
% 3.02/3.21             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.02/3.21  thf('44', plain,
% 3.02/3.21      (![X25 : $i, X26 : $i]:
% 3.02/3.21         (~ (m1_pre_topc @ X25 @ X26)
% 3.02/3.21          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 3.02/3.21             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 3.02/3.21          | ~ (l1_pre_topc @ X26))),
% 3.02/3.21      inference('cnf', [status(esa)], [t1_tsep_1])).
% 3.02/3.21  thf('45', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B)
% 3.02/3.21        | ~ (l1_pre_topc @ sk_A)
% 3.02/3.21        | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 3.02/3.21           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.02/3.21      inference('sup-', [status(thm)], ['43', '44'])).
% 3.02/3.21  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('47', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B)
% 3.02/3.21        | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 3.02/3.21           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.02/3.21      inference('demod', [status(thm)], ['45', '46'])).
% 3.02/3.21  thf(t26_tex_2, axiom,
% 3.02/3.21    (![A:$i]:
% 3.02/3.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 3.02/3.21       ( ![B:$i]:
% 3.02/3.21         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 3.02/3.21           ( ![C:$i]:
% 3.02/3.21             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.02/3.21               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 3.02/3.21                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 3.02/3.21  thf('48', plain,
% 3.02/3.21      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.02/3.21         ((v2_struct_0 @ X32)
% 3.02/3.21          | ~ (m1_pre_topc @ X32 @ X33)
% 3.02/3.21          | ((X34) != (u1_struct_0 @ X32))
% 3.02/3.21          | ~ (v1_tdlat_3 @ X32)
% 3.02/3.21          | (v2_tex_2 @ X34 @ X33)
% 3.02/3.21          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 3.02/3.21          | ~ (l1_pre_topc @ X33)
% 3.02/3.21          | (v2_struct_0 @ X33))),
% 3.02/3.21      inference('cnf', [status(esa)], [t26_tex_2])).
% 3.02/3.21  thf('49', plain,
% 3.02/3.21      (![X32 : $i, X33 : $i]:
% 3.02/3.21         ((v2_struct_0 @ X33)
% 3.02/3.21          | ~ (l1_pre_topc @ X33)
% 3.02/3.21          | ~ (m1_subset_1 @ (u1_struct_0 @ X32) @ 
% 3.02/3.21               (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 3.02/3.21          | (v2_tex_2 @ (u1_struct_0 @ X32) @ X33)
% 3.02/3.21          | ~ (v1_tdlat_3 @ X32)
% 3.02/3.21          | ~ (m1_pre_topc @ X32 @ X33)
% 3.02/3.21          | (v2_struct_0 @ X32))),
% 3.02/3.21      inference('simplify', [status(thm)], ['48'])).
% 3.02/3.21  thf('50', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 3.02/3.21        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 3.02/3.21        | ~ (l1_pre_topc @ sk_A)
% 3.02/3.21        | (v2_struct_0 @ sk_A))),
% 3.02/3.21      inference('sup-', [status(thm)], ['47', '49'])).
% 3.02/3.21  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('52', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 3.02/3.21        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 3.02/3.21        | (v2_struct_0 @ sk_A))),
% 3.02/3.21      inference('demod', [status(thm)], ['50', '51'])).
% 3.02/3.21  thf('53', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 3.02/3.21        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['42', '52'])).
% 3.02/3.21  thf('54', plain,
% 3.02/3.21      (((v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('simplify', [status(thm)], ['53'])).
% 3.02/3.21  thf('55', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 3.02/3.21        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['41', '54'])).
% 3.02/3.21  thf('56', plain,
% 3.02/3.21      (((v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('simplify', [status(thm)], ['55'])).
% 3.02/3.21  thf('57', plain,
% 3.02/3.21      (((v2_tex_2 @ sk_B @ sk_A)
% 3.02/3.21        | (v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 3.02/3.21      inference('sup+', [status(thm)], ['26', '56'])).
% 3.02/3.21  thf('58', plain,
% 3.02/3.21      (((v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | (v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v2_tex_2 @ sk_B @ sk_A))),
% 3.02/3.21      inference('simplify', [status(thm)], ['57'])).
% 3.02/3.21  thf('59', plain,
% 3.02/3.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('60', plain,
% 3.02/3.21      (![X30 : $i, X31 : $i]:
% 3.02/3.21         ((v1_xboole_0 @ X30)
% 3.02/3.21          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 3.02/3.21          | ~ (v2_struct_0 @ (sk_C_1 @ X30 @ X31))
% 3.02/3.21          | ~ (l1_pre_topc @ X31)
% 3.02/3.21          | (v2_struct_0 @ X31))),
% 3.02/3.21      inference('cnf', [status(esa)], [t10_tsep_1])).
% 3.02/3.21  thf('61', plain,
% 3.02/3.21      (((v2_struct_0 @ sk_A)
% 3.02/3.21        | ~ (l1_pre_topc @ sk_A)
% 3.02/3.21        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['59', '60'])).
% 3.02/3.21  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('63', plain,
% 3.02/3.21      (((v2_struct_0 @ sk_A)
% 3.02/3.21        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A))
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('demod', [status(thm)], ['61', '62'])).
% 3.02/3.21  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('65', plain,
% 3.02/3.21      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B @ sk_A)))),
% 3.02/3.21      inference('clc', [status(thm)], ['63', '64'])).
% 3.02/3.21  thf('66', plain,
% 3.02/3.21      (((v2_tex_2 @ sk_B @ sk_A)
% 3.02/3.21        | (v1_xboole_0 @ sk_B)
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['58', '65'])).
% 3.02/3.21  thf('67', plain,
% 3.02/3.21      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 3.02/3.21      inference('simplify', [status(thm)], ['66'])).
% 3.02/3.21  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('69', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('clc', [status(thm)], ['67', '68'])).
% 3.02/3.21  thf('70', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('71', plain, ((v1_xboole_0 @ sk_B)),
% 3.02/3.21      inference('clc', [status(thm)], ['69', '70'])).
% 3.02/3.21  thf('72', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 3.02/3.21      inference('demod', [status(thm)], ['19', '71'])).
% 3.02/3.21  thf('73', plain,
% 3.02/3.21      (![X1 : $i, X3 : $i]:
% 3.02/3.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.02/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.02/3.21  thf('74', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['12', '15'])).
% 3.02/3.21  thf(t3_subset, axiom,
% 3.02/3.21    (![A:$i,B:$i]:
% 3.02/3.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.02/3.21  thf('75', plain,
% 3.02/3.21      (![X17 : $i, X19 : $i]:
% 3.02/3.21         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 3.02/3.21      inference('cnf', [status(esa)], [t3_subset])).
% 3.02/3.21  thf('76', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['74', '75'])).
% 3.02/3.21  thf('77', plain,
% 3.02/3.21      (![X23 : $i, X24 : $i]:
% 3.02/3.21         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 3.02/3.21          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ X23)
% 3.02/3.21          | ~ (l1_pre_topc @ X24))),
% 3.02/3.21      inference('cnf', [status(esa)], [t44_tops_1])).
% 3.02/3.21  thf('78', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X1)
% 3.02/3.21          | ~ (l1_pre_topc @ X0)
% 3.02/3.21          | (r1_tarski @ (k1_tops_1 @ X0 @ X1) @ X1))),
% 3.02/3.21      inference('sup-', [status(thm)], ['76', '77'])).
% 3.02/3.21  thf('79', plain,
% 3.02/3.21      (![X17 : $i, X19 : $i]:
% 3.02/3.21         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 3.02/3.21      inference('cnf', [status(esa)], [t3_subset])).
% 3.02/3.21  thf('80', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (~ (l1_pre_topc @ X1)
% 3.02/3.21          | ~ (v1_xboole_0 @ X0)
% 3.02/3.21          | (m1_subset_1 @ (k1_tops_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['78', '79'])).
% 3.02/3.21  thf('81', plain,
% 3.02/3.21      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X20 @ X21)
% 3.02/3.21          | ~ (v1_xboole_0 @ X22)
% 3.02/3.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 3.02/3.21      inference('cnf', [status(esa)], [t5_subset])).
% 3.02/3.21  thf('82', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X0)
% 3.02/3.21          | ~ (l1_pre_topc @ X1)
% 3.02/3.21          | ~ (v1_xboole_0 @ X0)
% 3.02/3.21          | ~ (r2_hidden @ X2 @ (k1_tops_1 @ X1 @ X0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['80', '81'])).
% 3.02/3.21  thf('83', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X2 @ (k1_tops_1 @ X1 @ X0))
% 3.02/3.21          | ~ (l1_pre_topc @ X1)
% 3.02/3.21          | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('simplify', [status(thm)], ['82'])).
% 3.02/3.21  thf('84', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         ((r1_tarski @ (k1_tops_1 @ X1 @ X0) @ X2)
% 3.02/3.21          | ~ (v1_xboole_0 @ X0)
% 3.02/3.21          | ~ (l1_pre_topc @ X1))),
% 3.02/3.21      inference('sup-', [status(thm)], ['73', '83'])).
% 3.02/3.21  thf('85', plain,
% 3.02/3.21      (![X17 : $i, X19 : $i]:
% 3.02/3.21         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 3.02/3.21      inference('cnf', [status(esa)], [t3_subset])).
% 3.02/3.21  thf('86', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         (~ (l1_pre_topc @ X2)
% 3.02/3.21          | ~ (v1_xboole_0 @ X1)
% 3.02/3.21          | (m1_subset_1 @ (k1_tops_1 @ X2 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['84', '85'])).
% 3.02/3.21  thf('87', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ X0))
% 3.02/3.21          | ~ (v1_xboole_0 @ sk_B)
% 3.02/3.21          | ~ (l1_pre_topc @ sk_A))),
% 3.02/3.21      inference('sup+', [status(thm)], ['72', '86'])).
% 3.02/3.21  thf('88', plain, ((v1_xboole_0 @ sk_B)),
% 3.02/3.21      inference('clc', [status(thm)], ['69', '70'])).
% 3.02/3.21  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('90', plain, (![X0 : $i]: (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ X0))),
% 3.02/3.21      inference('demod', [status(thm)], ['87', '88', '89'])).
% 3.02/3.21  thf('91', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 3.02/3.21      inference('demod', [status(thm)], ['3', '4'])).
% 3.02/3.21  thf(t29_tex_2, axiom,
% 3.02/3.21    (![A:$i]:
% 3.02/3.21     ( ( l1_pre_topc @ A ) =>
% 3.02/3.21       ( ![B:$i]:
% 3.02/3.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.02/3.21           ( ![C:$i]:
% 3.02/3.21             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.02/3.21               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 3.02/3.21                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 3.02/3.21  thf('92', plain,
% 3.02/3.21      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.02/3.21         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.02/3.21          | ~ (v2_tex_2 @ X37 @ X38)
% 3.02/3.21          | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ X38) @ X37 @ X39) @ X38)
% 3.02/3.21          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 3.02/3.21          | ~ (l1_pre_topc @ X38))),
% 3.02/3.21      inference('cnf', [status(esa)], [t29_tex_2])).
% 3.02/3.21  thf('93', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (~ (l1_pre_topc @ X0)
% 3.02/3.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.02/3.21          | (v2_tex_2 @ 
% 3.02/3.21             (k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ X0)
% 3.02/3.21          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['91', '92'])).
% 3.02/3.21  thf('94', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 3.02/3.21          | (v2_tex_2 @ 
% 3.02/3.21             (k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ sk_B) @ 
% 3.02/3.21             X0)
% 3.02/3.21          | ~ (l1_pre_topc @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['90', '93'])).
% 3.02/3.21  thf('95', plain, ((v1_xboole_0 @ sk_B)),
% 3.02/3.21      inference('clc', [status(thm)], ['69', '70'])).
% 3.02/3.21  thf('96', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 3.02/3.21      inference('demod', [status(thm)], ['3', '4'])).
% 3.02/3.21  thf(redefinition_k9_subset_1, axiom,
% 3.02/3.21    (![A:$i,B:$i,C:$i]:
% 3.02/3.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.21       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 3.02/3.21  thf('97', plain,
% 3.02/3.21      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.02/3.21         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 3.02/3.21          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.02/3.21      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 3.02/3.21  thf('98', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['96', '97'])).
% 3.02/3.21  thf('99', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 3.02/3.21      inference('demod', [status(thm)], ['3', '4'])).
% 3.02/3.21  thf(dt_k9_subset_1, axiom,
% 3.02/3.21    (![A:$i,B:$i,C:$i]:
% 3.02/3.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.02/3.21       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.02/3.21  thf('100', plain,
% 3.02/3.21      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.02/3.21         ((m1_subset_1 @ (k9_subset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X9))
% 3.02/3.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X9)))),
% 3.02/3.21      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 3.02/3.21  thf('101', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['99', '100'])).
% 3.02/3.21  thf('102', plain,
% 3.02/3.21      (![X17 : $i, X18 : $i]:
% 3.02/3.21         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 3.02/3.21      inference('cnf', [status(esa)], [t3_subset])).
% 3.02/3.21  thf('103', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 3.02/3.21      inference('sup-', [status(thm)], ['101', '102'])).
% 3.02/3.21  thf('104', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['16', '17'])).
% 3.02/3.21  thf('105', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (((k9_subset_1 @ X0 @ X1 @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['103', '104'])).
% 3.02/3.21  thf('106', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (((k3_xboole_0 @ X1 @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('sup+', [status(thm)], ['98', '105'])).
% 3.02/3.21  thf('107', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['95', '106'])).
% 3.02/3.21  thf('108', plain,
% 3.02/3.21      (![X1 : $i, X3 : $i]:
% 3.02/3.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.02/3.21      inference('cnf', [status(esa)], [d3_tarski])).
% 3.02/3.21  thf('109', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['99', '100'])).
% 3.02/3.21  thf('110', plain,
% 3.02/3.21      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.02/3.21         (~ (r2_hidden @ X20 @ X21)
% 3.02/3.21          | ~ (v1_xboole_0 @ X22)
% 3.02/3.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 3.02/3.21      inference('cnf', [status(esa)], [t5_subset])).
% 3.02/3.21  thf('111', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X0)
% 3.02/3.21          | ~ (r2_hidden @ X2 @ (k9_subset_1 @ X0 @ X1 @ X0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['109', '110'])).
% 3.02/3.21  thf('112', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['96', '97'])).
% 3.02/3.21  thf('113', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.02/3.21      inference('demod', [status(thm)], ['111', '112'])).
% 3.02/3.21  thf('114', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['108', '113'])).
% 3.02/3.21  thf('115', plain,
% 3.02/3.21      (![X17 : $i, X19 : $i]:
% 3.02/3.21         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 3.02/3.21      inference('cnf', [status(esa)], [t3_subset])).
% 3.02/3.21  thf('116', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X1)
% 3.02/3.21          | (m1_subset_1 @ (k3_xboole_0 @ X2 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['114', '115'])).
% 3.02/3.21  thf('117', plain,
% 3.02/3.21      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.02/3.21         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 3.02/3.21          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.02/3.21      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 3.02/3.21  thf('118', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X1)
% 3.02/3.21          | ((k9_subset_1 @ X0 @ X3 @ (k3_xboole_0 @ X2 @ X1))
% 3.02/3.21              = (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ X1))))),
% 3.02/3.21      inference('sup-', [status(thm)], ['116', '117'])).
% 3.02/3.21  thf('119', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.21         (((k9_subset_1 @ X2 @ X1 @ sk_B)
% 3.02/3.21            = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_B)))
% 3.02/3.21          | ~ (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('sup+', [status(thm)], ['107', '118'])).
% 3.02/3.21  thf('120', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['95', '106'])).
% 3.02/3.21  thf('121', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B) = (sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['95', '106'])).
% 3.02/3.21  thf('122', plain, ((v1_xboole_0 @ sk_B)),
% 3.02/3.21      inference('clc', [status(thm)], ['69', '70'])).
% 3.02/3.21  thf('123', plain,
% 3.02/3.21      (![X1 : $i, X2 : $i]: ((k9_subset_1 @ X2 @ X1 @ sk_B) = (sk_B))),
% 3.02/3.21      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 3.02/3.21  thf('124', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 3.02/3.21          | (v2_tex_2 @ sk_B @ X0)
% 3.02/3.21          | ~ (l1_pre_topc @ X0))),
% 3.02/3.21      inference('demod', [status(thm)], ['94', '123'])).
% 3.02/3.21  thf('125', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         (~ (v1_tdlat_3 @ X0)
% 3.02/3.21          | ~ (l1_pre_topc @ X0)
% 3.02/3.21          | (v2_struct_0 @ X0)
% 3.02/3.21          | ~ (l1_pre_topc @ X0)
% 3.02/3.21          | (v2_tex_2 @ sk_B @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['6', '124'])).
% 3.02/3.21  thf('126', plain,
% 3.02/3.21      (![X0 : $i]:
% 3.02/3.21         ((v2_tex_2 @ sk_B @ X0)
% 3.02/3.21          | (v2_struct_0 @ X0)
% 3.02/3.21          | ~ (l1_pre_topc @ X0)
% 3.02/3.21          | ~ (v1_tdlat_3 @ X0))),
% 3.02/3.21      inference('simplify', [status(thm)], ['125'])).
% 3.02/3.21  thf('127', plain, ((v1_xboole_0 @ sk_B)),
% 3.02/3.21      inference('clc', [status(thm)], ['69', '70'])).
% 3.02/3.21  thf('128', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['12', '15'])).
% 3.02/3.21  thf('129', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.02/3.21      inference('sup-', [status(thm)], ['16', '17'])).
% 3.02/3.21  thf('130', plain,
% 3.02/3.21      (![X0 : $i, X1 : $i]:
% 3.02/3.21         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['128', '129'])).
% 3.02/3.21  thf('131', plain, (![X0 : $i]: (((X0) = (sk_B)) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['127', '130'])).
% 3.02/3.21  thf('132', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('133', plain,
% 3.02/3.21      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.21      inference('sup-', [status(thm)], ['131', '132'])).
% 3.02/3.21  thf('134', plain,
% 3.02/3.21      ((~ (v1_tdlat_3 @ sk_A)
% 3.02/3.21        | ~ (l1_pre_topc @ sk_A)
% 3.02/3.21        | (v2_struct_0 @ sk_A)
% 3.02/3.21        | ~ (v1_xboole_0 @ sk_B))),
% 3.02/3.21      inference('sup-', [status(thm)], ['126', '133'])).
% 3.02/3.21  thf('135', plain, ((v1_tdlat_3 @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 3.02/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.21  thf('137', plain, ((v1_xboole_0 @ sk_B)),
% 3.02/3.21      inference('clc', [status(thm)], ['69', '70'])).
% 3.02/3.21  thf('138', plain, ((v2_struct_0 @ sk_A)),
% 3.02/3.21      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 3.02/3.21  thf('139', plain, ($false), inference('demod', [status(thm)], ['0', '138'])).
% 3.02/3.21  
% 3.02/3.21  % SZS output end Refutation
% 3.02/3.21  
% 3.02/3.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
