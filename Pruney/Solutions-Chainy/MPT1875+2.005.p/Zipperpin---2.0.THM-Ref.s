%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2pKfeeIjtQ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:51 EST 2020

% Result     : Theorem 8.22s
% Output     : Refutation 8.22s
% Verified   : 
% Statistics : Number of formulae       :  156 (1233 expanded)
%              Number of leaves         :   37 ( 356 expanded)
%              Depth                    :   29
%              Number of atoms          : 1157 (13570 expanded)
%              Number of equality atoms :   30 ( 178 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X37: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X37 ) @ X37 )
      | ~ ( v1_tdlat_3 @ X37 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( X31
        = ( u1_struct_0 @ ( sk_C_1 @ X31 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X31 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v1_tdlat_3 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v1_tdlat_3 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

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

thf('35',plain,(
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

thf('36',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X33 ) @ X34 )
      | ~ ( v1_tdlat_3 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X31 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k9_subset_1 @ X18 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['63','66'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('70',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['58','75'])).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('79',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['76','85'])).

thf('87',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['56','57'])).

thf('88',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
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

thf('90',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v2_tex_2 @ X38 @ X39 )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t29_tex_2])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ sk_B_2 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['58','75'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('95',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k9_subset_1 @ X18 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k9_subset_1 @ X0 @ X3 @ ( k3_xboole_0 @ X2 @ X1 ) )
        = ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X2 @ X1 @ sk_B_2 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_B_2 ) ) )
      | ~ ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['58','75'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['58','75'])).

thf('100',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['56','57'])).

thf('101',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X2 @ X1 @ sk_B_2 )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_tex_2 @ sk_B_2 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['92','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['56','57'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['104','111'])).

thf('113',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['56','57'])).

thf('116',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['0','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2pKfeeIjtQ
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 8.22/8.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.22/8.45  % Solved by: fo/fo7.sh
% 8.22/8.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.22/8.45  % done 11270 iterations in 7.983s
% 8.22/8.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.22/8.45  % SZS output start Refutation
% 8.22/8.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.22/8.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.22/8.45  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 8.22/8.45  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 8.22/8.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.22/8.45  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 8.22/8.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.22/8.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.22/8.45  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 8.22/8.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.22/8.45  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 8.22/8.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.22/8.45  thf(sk_A_type, type, sk_A: $i).
% 8.22/8.45  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 8.22/8.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.22/8.45  thf(sk_B_2_type, type, sk_B_2: $i).
% 8.22/8.45  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 8.22/8.45  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 8.22/8.45  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 8.22/8.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.22/8.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.22/8.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.22/8.45  thf(t43_tex_2, conjecture,
% 8.22/8.45    (![A:$i]:
% 8.22/8.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 8.22/8.45         ( l1_pre_topc @ A ) ) =>
% 8.22/8.45       ( ![B:$i]:
% 8.22/8.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.22/8.45           ( v2_tex_2 @ B @ A ) ) ) ))).
% 8.22/8.45  thf(zf_stmt_0, negated_conjecture,
% 8.22/8.45    (~( ![A:$i]:
% 8.22/8.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 8.22/8.45            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.22/8.45          ( ![B:$i]:
% 8.22/8.45            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.22/8.45              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 8.22/8.45    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 8.22/8.45  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf(t27_tex_2, axiom,
% 8.22/8.45    (![A:$i]:
% 8.22/8.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 8.22/8.45       ( ![B:$i]:
% 8.22/8.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.22/8.45           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 8.22/8.45             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 8.22/8.45  thf('1', plain,
% 8.22/8.45      (![X36 : $i, X37 : $i]:
% 8.22/8.45         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 8.22/8.45          | ~ (v1_tdlat_3 @ X37)
% 8.22/8.45          | (v2_tex_2 @ X36 @ X37)
% 8.22/8.45          | ((X36) != (u1_struct_0 @ X37))
% 8.22/8.45          | ~ (l1_pre_topc @ X37)
% 8.22/8.45          | (v2_struct_0 @ X37))),
% 8.22/8.45      inference('cnf', [status(esa)], [t27_tex_2])).
% 8.22/8.45  thf('2', plain,
% 8.22/8.45      (![X37 : $i]:
% 8.22/8.45         ((v2_struct_0 @ X37)
% 8.22/8.45          | ~ (l1_pre_topc @ X37)
% 8.22/8.45          | (v2_tex_2 @ (u1_struct_0 @ X37) @ X37)
% 8.22/8.45          | ~ (v1_tdlat_3 @ X37)
% 8.22/8.45          | ~ (m1_subset_1 @ (u1_struct_0 @ X37) @ 
% 8.22/8.45               (k1_zfmisc_1 @ (u1_struct_0 @ X37))))),
% 8.22/8.45      inference('simplify', [status(thm)], ['1'])).
% 8.22/8.45  thf(dt_k2_subset_1, axiom,
% 8.22/8.45    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 8.22/8.45  thf('3', plain,
% 8.22/8.45      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 8.22/8.45      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 8.22/8.45  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 8.22/8.45  thf('4', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 8.22/8.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 8.22/8.45  thf('5', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 8.22/8.45      inference('demod', [status(thm)], ['3', '4'])).
% 8.22/8.45  thf('6', plain,
% 8.22/8.45      (![X37 : $i]:
% 8.22/8.45         ((v2_struct_0 @ X37)
% 8.22/8.45          | ~ (l1_pre_topc @ X37)
% 8.22/8.45          | (v2_tex_2 @ (u1_struct_0 @ X37) @ X37)
% 8.22/8.45          | ~ (v1_tdlat_3 @ X37))),
% 8.22/8.45      inference('demod', [status(thm)], ['2', '5'])).
% 8.22/8.45  thf('7', plain,
% 8.22/8.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf(t10_tsep_1, axiom,
% 8.22/8.45    (![A:$i]:
% 8.22/8.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 8.22/8.45       ( ![B:$i]:
% 8.22/8.45         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 8.22/8.45             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.22/8.45           ( ?[C:$i]:
% 8.22/8.45             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 8.22/8.45               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 8.22/8.45  thf('8', plain,
% 8.22/8.45      (![X31 : $i, X32 : $i]:
% 8.22/8.45         ((v1_xboole_0 @ X31)
% 8.22/8.45          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 8.22/8.45          | ((X31) = (u1_struct_0 @ (sk_C_1 @ X31 @ X32)))
% 8.22/8.45          | ~ (l1_pre_topc @ X32)
% 8.22/8.45          | (v2_struct_0 @ X32))),
% 8.22/8.45      inference('cnf', [status(esa)], [t10_tsep_1])).
% 8.22/8.45  thf('9', plain,
% 8.22/8.45      (((v2_struct_0 @ sk_A)
% 8.22/8.45        | ~ (l1_pre_topc @ sk_A)
% 8.22/8.45        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['7', '8'])).
% 8.22/8.45  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('11', plain,
% 8.22/8.45      (((v2_struct_0 @ sk_A)
% 8.22/8.45        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('demod', [status(thm)], ['9', '10'])).
% 8.22/8.45  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('13', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))))),
% 8.22/8.45      inference('clc', [status(thm)], ['11', '12'])).
% 8.22/8.45  thf('14', plain,
% 8.22/8.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('15', plain,
% 8.22/8.45      (![X31 : $i, X32 : $i]:
% 8.22/8.45         ((v1_xboole_0 @ X31)
% 8.22/8.45          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 8.22/8.45          | (m1_pre_topc @ (sk_C_1 @ X31 @ X32) @ X32)
% 8.22/8.45          | ~ (l1_pre_topc @ X32)
% 8.22/8.45          | (v2_struct_0 @ X32))),
% 8.22/8.45      inference('cnf', [status(esa)], [t10_tsep_1])).
% 8.22/8.45  thf('16', plain,
% 8.22/8.45      (((v2_struct_0 @ sk_A)
% 8.22/8.45        | ~ (l1_pre_topc @ sk_A)
% 8.22/8.45        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['14', '15'])).
% 8.22/8.45  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('18', plain,
% 8.22/8.45      (((v2_struct_0 @ sk_A)
% 8.22/8.45        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('demod', [status(thm)], ['16', '17'])).
% 8.22/8.45  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('20', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))),
% 8.22/8.45      inference('clc', [status(thm)], ['18', '19'])).
% 8.22/8.45  thf(cc5_tdlat_3, axiom,
% 8.22/8.45    (![A:$i]:
% 8.22/8.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 8.22/8.45         ( l1_pre_topc @ A ) ) =>
% 8.22/8.45       ( ![B:$i]:
% 8.22/8.45         ( ( m1_pre_topc @ B @ A ) =>
% 8.22/8.45           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 8.22/8.45             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 8.22/8.45  thf('21', plain,
% 8.22/8.45      (![X29 : $i, X30 : $i]:
% 8.22/8.45         (~ (m1_pre_topc @ X29 @ X30)
% 8.22/8.45          | (v1_tdlat_3 @ X29)
% 8.22/8.45          | ~ (l1_pre_topc @ X30)
% 8.22/8.45          | ~ (v1_tdlat_3 @ X30)
% 8.22/8.45          | ~ (v2_pre_topc @ X30)
% 8.22/8.45          | (v2_struct_0 @ X30))),
% 8.22/8.45      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 8.22/8.45  thf('22', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | ~ (v2_pre_topc @ sk_A)
% 8.22/8.45        | ~ (v1_tdlat_3 @ sk_A)
% 8.22/8.45        | ~ (l1_pre_topc @ sk_A)
% 8.22/8.45        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 8.22/8.45      inference('sup-', [status(thm)], ['20', '21'])).
% 8.22/8.45  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('24', plain, ((v1_tdlat_3 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('26', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 8.22/8.45      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 8.22/8.45  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('28', plain,
% 8.22/8.45      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A)) | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('clc', [status(thm)], ['26', '27'])).
% 8.22/8.45  thf('29', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))),
% 8.22/8.45      inference('clc', [status(thm)], ['18', '19'])).
% 8.22/8.45  thf('30', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))),
% 8.22/8.45      inference('clc', [status(thm)], ['18', '19'])).
% 8.22/8.45  thf(t1_tsep_1, axiom,
% 8.22/8.45    (![A:$i]:
% 8.22/8.45     ( ( l1_pre_topc @ A ) =>
% 8.22/8.45       ( ![B:$i]:
% 8.22/8.45         ( ( m1_pre_topc @ B @ A ) =>
% 8.22/8.45           ( m1_subset_1 @
% 8.22/8.45             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 8.22/8.45  thf('31', plain,
% 8.22/8.45      (![X26 : $i, X27 : $i]:
% 8.22/8.45         (~ (m1_pre_topc @ X26 @ X27)
% 8.22/8.45          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 8.22/8.45             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 8.22/8.45          | ~ (l1_pre_topc @ X27))),
% 8.22/8.45      inference('cnf', [status(esa)], [t1_tsep_1])).
% 8.22/8.45  thf('32', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | ~ (l1_pre_topc @ sk_A)
% 8.22/8.45        | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 8.22/8.45           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.22/8.45      inference('sup-', [status(thm)], ['30', '31'])).
% 8.22/8.45  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('34', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 8.22/8.45           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.22/8.45      inference('demod', [status(thm)], ['32', '33'])).
% 8.22/8.45  thf(t26_tex_2, axiom,
% 8.22/8.45    (![A:$i]:
% 8.22/8.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 8.22/8.45       ( ![B:$i]:
% 8.22/8.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 8.22/8.45           ( ![C:$i]:
% 8.22/8.45             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.22/8.45               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 8.22/8.45                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 8.22/8.45  thf('35', plain,
% 8.22/8.45      (![X33 : $i, X34 : $i, X35 : $i]:
% 8.22/8.45         ((v2_struct_0 @ X33)
% 8.22/8.45          | ~ (m1_pre_topc @ X33 @ X34)
% 8.22/8.45          | ((X35) != (u1_struct_0 @ X33))
% 8.22/8.45          | ~ (v1_tdlat_3 @ X33)
% 8.22/8.45          | (v2_tex_2 @ X35 @ X34)
% 8.22/8.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 8.22/8.45          | ~ (l1_pre_topc @ X34)
% 8.22/8.45          | (v2_struct_0 @ X34))),
% 8.22/8.45      inference('cnf', [status(esa)], [t26_tex_2])).
% 8.22/8.45  thf('36', plain,
% 8.22/8.45      (![X33 : $i, X34 : $i]:
% 8.22/8.45         ((v2_struct_0 @ X34)
% 8.22/8.45          | ~ (l1_pre_topc @ X34)
% 8.22/8.45          | ~ (m1_subset_1 @ (u1_struct_0 @ X33) @ 
% 8.22/8.45               (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 8.22/8.45          | (v2_tex_2 @ (u1_struct_0 @ X33) @ X34)
% 8.22/8.45          | ~ (v1_tdlat_3 @ X33)
% 8.22/8.45          | ~ (m1_pre_topc @ X33 @ X34)
% 8.22/8.45          | (v2_struct_0 @ X33))),
% 8.22/8.45      inference('simplify', [status(thm)], ['35'])).
% 8.22/8.45  thf('37', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 8.22/8.45        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A)
% 8.22/8.45        | ~ (l1_pre_topc @ sk_A)
% 8.22/8.45        | (v2_struct_0 @ sk_A))),
% 8.22/8.45      inference('sup-', [status(thm)], ['34', '36'])).
% 8.22/8.45  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('39', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 8.22/8.45        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A)
% 8.22/8.45        | (v2_struct_0 @ sk_A))),
% 8.22/8.45      inference('demod', [status(thm)], ['37', '38'])).
% 8.22/8.45  thf('40', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A)
% 8.22/8.45        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['29', '39'])).
% 8.22/8.45  thf('41', plain,
% 8.22/8.45      (((v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A)
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('simplify', [status(thm)], ['40'])).
% 8.22/8.45  thf('42', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A)
% 8.22/8.45        | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 8.22/8.45      inference('sup-', [status(thm)], ['28', '41'])).
% 8.22/8.45  thf('43', plain,
% 8.22/8.45      (((v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A)
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('simplify', [status(thm)], ['42'])).
% 8.22/8.45  thf('44', plain,
% 8.22/8.45      (((v2_tex_2 @ sk_B_2 @ sk_A)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 8.22/8.45      inference('sup+', [status(thm)], ['13', '43'])).
% 8.22/8.45  thf('45', plain,
% 8.22/8.45      (((v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 8.22/8.45      inference('simplify', [status(thm)], ['44'])).
% 8.22/8.45  thf('46', plain,
% 8.22/8.45      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('47', plain,
% 8.22/8.45      (![X31 : $i, X32 : $i]:
% 8.22/8.45         ((v1_xboole_0 @ X31)
% 8.22/8.45          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 8.22/8.45          | ~ (v2_struct_0 @ (sk_C_1 @ X31 @ X32))
% 8.22/8.45          | ~ (l1_pre_topc @ X32)
% 8.22/8.45          | (v2_struct_0 @ X32))),
% 8.22/8.45      inference('cnf', [status(esa)], [t10_tsep_1])).
% 8.22/8.45  thf('48', plain,
% 8.22/8.45      (((v2_struct_0 @ sk_A)
% 8.22/8.45        | ~ (l1_pre_topc @ sk_A)
% 8.22/8.45        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['46', '47'])).
% 8.22/8.45  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('50', plain,
% 8.22/8.45      (((v2_struct_0 @ sk_A)
% 8.22/8.45        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('demod', [status(thm)], ['48', '49'])).
% 8.22/8.45  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('52', plain,
% 8.22/8.45      (((v1_xboole_0 @ sk_B_2) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 8.22/8.45      inference('clc', [status(thm)], ['50', '51'])).
% 8.22/8.45  thf('53', plain,
% 8.22/8.45      (((v2_tex_2 @ sk_B_2 @ sk_A)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['45', '52'])).
% 8.22/8.45  thf('54', plain,
% 8.22/8.45      (((v2_struct_0 @ sk_A)
% 8.22/8.45        | (v1_xboole_0 @ sk_B_2)
% 8.22/8.45        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 8.22/8.45      inference('simplify', [status(thm)], ['53'])).
% 8.22/8.45  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('56', plain, (((v2_tex_2 @ sk_B_2 @ sk_A) | (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('clc', [status(thm)], ['54', '55'])).
% 8.22/8.45  thf('57', plain, (~ (v2_tex_2 @ sk_B_2 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('58', plain, ((v1_xboole_0 @ sk_B_2)),
% 8.22/8.45      inference('clc', [status(thm)], ['56', '57'])).
% 8.22/8.45  thf('59', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 8.22/8.45      inference('demod', [status(thm)], ['3', '4'])).
% 8.22/8.45  thf(dt_k9_subset_1, axiom,
% 8.22/8.45    (![A:$i,B:$i,C:$i]:
% 8.22/8.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.22/8.45       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.22/8.45  thf('60', plain,
% 8.22/8.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 8.22/8.45         ((m1_subset_1 @ (k9_subset_1 @ X12 @ X13 @ X14) @ (k1_zfmisc_1 @ X12))
% 8.22/8.45          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X12)))),
% 8.22/8.45      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 8.22/8.45  thf('61', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]:
% 8.22/8.45         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['59', '60'])).
% 8.22/8.45  thf(t3_subset, axiom,
% 8.22/8.45    (![A:$i,B:$i]:
% 8.22/8.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.22/8.45  thf('62', plain,
% 8.22/8.45      (![X19 : $i, X20 : $i]:
% 8.22/8.45         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 8.22/8.45      inference('cnf', [status(esa)], [t3_subset])).
% 8.22/8.45  thf('63', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 8.22/8.45      inference('sup-', [status(thm)], ['61', '62'])).
% 8.22/8.45  thf('64', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 8.22/8.45      inference('demod', [status(thm)], ['3', '4'])).
% 8.22/8.45  thf(redefinition_k9_subset_1, axiom,
% 8.22/8.45    (![A:$i,B:$i,C:$i]:
% 8.22/8.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.22/8.45       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 8.22/8.45  thf('65', plain,
% 8.22/8.45      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.22/8.45         (((k9_subset_1 @ X18 @ X16 @ X17) = (k3_xboole_0 @ X16 @ X17))
% 8.22/8.45          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 8.22/8.45      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 8.22/8.45  thf('66', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]:
% 8.22/8.45         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['64', '65'])).
% 8.22/8.45  thf('67', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 8.22/8.45      inference('demod', [status(thm)], ['63', '66'])).
% 8.22/8.45  thf(d3_tarski, axiom,
% 8.22/8.45    (![A:$i,B:$i]:
% 8.22/8.45     ( ( r1_tarski @ A @ B ) <=>
% 8.22/8.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.22/8.45  thf('68', plain,
% 8.22/8.45      (![X1 : $i, X3 : $i]:
% 8.22/8.45         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.22/8.45      inference('cnf', [status(esa)], [d3_tarski])).
% 8.22/8.45  thf('69', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 8.22/8.45      inference('demod', [status(thm)], ['3', '4'])).
% 8.22/8.45  thf(t5_subset, axiom,
% 8.22/8.45    (![A:$i,B:$i,C:$i]:
% 8.22/8.45     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 8.22/8.45          ( v1_xboole_0 @ C ) ) ))).
% 8.22/8.45  thf('70', plain,
% 8.22/8.45      (![X22 : $i, X23 : $i, X24 : $i]:
% 8.22/8.45         (~ (r2_hidden @ X22 @ X23)
% 8.22/8.45          | ~ (v1_xboole_0 @ X24)
% 8.22/8.45          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 8.22/8.45      inference('cnf', [status(esa)], [t5_subset])).
% 8.22/8.45  thf('71', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['69', '70'])).
% 8.22/8.45  thf('72', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['68', '71'])).
% 8.22/8.45  thf(d10_xboole_0, axiom,
% 8.22/8.45    (![A:$i,B:$i]:
% 8.22/8.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.22/8.45  thf('73', plain,
% 8.22/8.45      (![X4 : $i, X6 : $i]:
% 8.22/8.45         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 8.22/8.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.22/8.45  thf('74', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]:
% 8.22/8.45         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 8.22/8.45      inference('sup-', [status(thm)], ['72', '73'])).
% 8.22/8.45  thf('75', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]:
% 8.22/8.45         (((k3_xboole_0 @ X1 @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['67', '74'])).
% 8.22/8.45  thf('76', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_2) = (sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['58', '75'])).
% 8.22/8.45  thf('77', plain,
% 8.22/8.45      (![X1 : $i, X3 : $i]:
% 8.22/8.45         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.22/8.45      inference('cnf', [status(esa)], [d3_tarski])).
% 8.22/8.45  thf('78', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]:
% 8.22/8.45         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['59', '60'])).
% 8.22/8.45  thf('79', plain,
% 8.22/8.45      (![X22 : $i, X23 : $i, X24 : $i]:
% 8.22/8.45         (~ (r2_hidden @ X22 @ X23)
% 8.22/8.45          | ~ (v1_xboole_0 @ X24)
% 8.22/8.45          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 8.22/8.45      inference('cnf', [status(esa)], [t5_subset])).
% 8.22/8.45  thf('80', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.22/8.45         (~ (v1_xboole_0 @ X0)
% 8.22/8.45          | ~ (r2_hidden @ X2 @ (k9_subset_1 @ X0 @ X1 @ X0)))),
% 8.22/8.45      inference('sup-', [status(thm)], ['78', '79'])).
% 8.22/8.45  thf('81', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]:
% 8.22/8.45         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['64', '65'])).
% 8.22/8.45  thf('82', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.22/8.45         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.22/8.45      inference('demod', [status(thm)], ['80', '81'])).
% 8.22/8.45  thf('83', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.22/8.45         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2) | ~ (v1_xboole_0 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['77', '82'])).
% 8.22/8.45  thf('84', plain,
% 8.22/8.45      (![X19 : $i, X21 : $i]:
% 8.22/8.45         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 8.22/8.45      inference('cnf', [status(esa)], [t3_subset])).
% 8.22/8.45  thf('85', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.22/8.45         (~ (v1_xboole_0 @ X1)
% 8.22/8.45          | (m1_subset_1 @ (k3_xboole_0 @ X2 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 8.22/8.45      inference('sup-', [status(thm)], ['83', '84'])).
% 8.22/8.45  thf('86', plain,
% 8.22/8.45      (![X0 : $i]:
% 8.22/8.45         ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ X0))
% 8.22/8.45          | ~ (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('sup+', [status(thm)], ['76', '85'])).
% 8.22/8.45  thf('87', plain, ((v1_xboole_0 @ sk_B_2)),
% 8.22/8.45      inference('clc', [status(thm)], ['56', '57'])).
% 8.22/8.45  thf('88', plain, (![X0 : $i]: (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ X0))),
% 8.22/8.45      inference('demod', [status(thm)], ['86', '87'])).
% 8.22/8.45  thf('89', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 8.22/8.45      inference('demod', [status(thm)], ['3', '4'])).
% 8.22/8.45  thf(t29_tex_2, axiom,
% 8.22/8.45    (![A:$i]:
% 8.22/8.45     ( ( l1_pre_topc @ A ) =>
% 8.22/8.45       ( ![B:$i]:
% 8.22/8.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.22/8.45           ( ![C:$i]:
% 8.22/8.45             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.22/8.45               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 8.22/8.45                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 8.22/8.45  thf('90', plain,
% 8.22/8.45      (![X38 : $i, X39 : $i, X40 : $i]:
% 8.22/8.45         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 8.22/8.45          | ~ (v2_tex_2 @ X38 @ X39)
% 8.22/8.45          | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ X39) @ X38 @ X40) @ X39)
% 8.22/8.45          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 8.22/8.45          | ~ (l1_pre_topc @ X39))),
% 8.22/8.45      inference('cnf', [status(esa)], [t29_tex_2])).
% 8.22/8.45  thf('91', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]:
% 8.22/8.45         (~ (l1_pre_topc @ X0)
% 8.22/8.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 8.22/8.45          | (v2_tex_2 @ 
% 8.22/8.45             (k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ X0)
% 8.22/8.45          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['89', '90'])).
% 8.22/8.45  thf('92', plain,
% 8.22/8.45      (![X0 : $i]:
% 8.22/8.45         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 8.22/8.45          | (v2_tex_2 @ 
% 8.22/8.45             (k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ sk_B_2) @ 
% 8.22/8.45             X0)
% 8.22/8.45          | ~ (l1_pre_topc @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['88', '91'])).
% 8.22/8.45  thf('93', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_2) = (sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['58', '75'])).
% 8.22/8.45  thf('94', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.22/8.45         (~ (v1_xboole_0 @ X1)
% 8.22/8.45          | (m1_subset_1 @ (k3_xboole_0 @ X2 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 8.22/8.45      inference('sup-', [status(thm)], ['83', '84'])).
% 8.22/8.45  thf('95', plain,
% 8.22/8.45      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.22/8.45         (((k9_subset_1 @ X18 @ X16 @ X17) = (k3_xboole_0 @ X16 @ X17))
% 8.22/8.45          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 8.22/8.45      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 8.22/8.45  thf('96', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.22/8.45         (~ (v1_xboole_0 @ X1)
% 8.22/8.45          | ((k9_subset_1 @ X0 @ X3 @ (k3_xboole_0 @ X2 @ X1))
% 8.22/8.45              = (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ X1))))),
% 8.22/8.45      inference('sup-', [status(thm)], ['94', '95'])).
% 8.22/8.45  thf('97', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.22/8.45         (((k9_subset_1 @ X2 @ X1 @ sk_B_2)
% 8.22/8.45            = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_B_2)))
% 8.22/8.45          | ~ (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('sup+', [status(thm)], ['93', '96'])).
% 8.22/8.45  thf('98', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_2) = (sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['58', '75'])).
% 8.22/8.45  thf('99', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_B_2) = (sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['58', '75'])).
% 8.22/8.45  thf('100', plain, ((v1_xboole_0 @ sk_B_2)),
% 8.22/8.45      inference('clc', [status(thm)], ['56', '57'])).
% 8.22/8.45  thf('101', plain,
% 8.22/8.45      (![X1 : $i, X2 : $i]: ((k9_subset_1 @ X2 @ X1 @ sk_B_2) = (sk_B_2))),
% 8.22/8.45      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 8.22/8.45  thf('102', plain,
% 8.22/8.45      (![X0 : $i]:
% 8.22/8.45         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 8.22/8.45          | (v2_tex_2 @ sk_B_2 @ X0)
% 8.22/8.45          | ~ (l1_pre_topc @ X0))),
% 8.22/8.45      inference('demod', [status(thm)], ['92', '101'])).
% 8.22/8.45  thf('103', plain,
% 8.22/8.45      (![X0 : $i]:
% 8.22/8.45         (~ (v1_tdlat_3 @ X0)
% 8.22/8.45          | ~ (l1_pre_topc @ X0)
% 8.22/8.45          | (v2_struct_0 @ X0)
% 8.22/8.45          | ~ (l1_pre_topc @ X0)
% 8.22/8.45          | (v2_tex_2 @ sk_B_2 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['6', '102'])).
% 8.22/8.45  thf('104', plain,
% 8.22/8.45      (![X0 : $i]:
% 8.22/8.45         ((v2_tex_2 @ sk_B_2 @ X0)
% 8.22/8.45          | (v2_struct_0 @ X0)
% 8.22/8.45          | ~ (l1_pre_topc @ X0)
% 8.22/8.45          | ~ (v1_tdlat_3 @ X0))),
% 8.22/8.45      inference('simplify', [status(thm)], ['103'])).
% 8.22/8.45  thf('105', plain, ((v1_xboole_0 @ sk_B_2)),
% 8.22/8.45      inference('clc', [status(thm)], ['56', '57'])).
% 8.22/8.45  thf('106', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['68', '71'])).
% 8.22/8.45  thf('107', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]:
% 8.22/8.45         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 8.22/8.45      inference('sup-', [status(thm)], ['72', '73'])).
% 8.22/8.45  thf('108', plain,
% 8.22/8.45      (![X0 : $i, X1 : $i]:
% 8.22/8.45         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['106', '107'])).
% 8.22/8.45  thf('109', plain, (![X0 : $i]: (((X0) = (sk_B_2)) | ~ (v1_xboole_0 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['105', '108'])).
% 8.22/8.45  thf('110', plain, (~ (v2_tex_2 @ sk_B_2 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('111', plain,
% 8.22/8.45      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 8.22/8.45      inference('sup-', [status(thm)], ['109', '110'])).
% 8.22/8.45  thf('112', plain,
% 8.22/8.45      ((~ (v1_tdlat_3 @ sk_A)
% 8.22/8.45        | ~ (l1_pre_topc @ sk_A)
% 8.22/8.45        | (v2_struct_0 @ sk_A)
% 8.22/8.45        | ~ (v1_xboole_0 @ sk_B_2))),
% 8.22/8.45      inference('sup-', [status(thm)], ['104', '111'])).
% 8.22/8.45  thf('113', plain, ((v1_tdlat_3 @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 8.22/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.22/8.45  thf('115', plain, ((v1_xboole_0 @ sk_B_2)),
% 8.22/8.45      inference('clc', [status(thm)], ['56', '57'])).
% 8.22/8.45  thf('116', plain, ((v2_struct_0 @ sk_A)),
% 8.22/8.45      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 8.22/8.45  thf('117', plain, ($false), inference('demod', [status(thm)], ['0', '116'])).
% 8.22/8.45  
% 8.22/8.45  % SZS output end Refutation
% 8.22/8.45  
% 8.22/8.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
