%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XZineNIhii

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:53 EST 2020

% Result     : Theorem 5.17s
% Output     : Refutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :  268 (2727 expanded)
%              Number of leaves         :   31 ( 792 expanded)
%              Depth                    :   35
%              Number of atoms          : 2228 (30173 expanded)
%              Number of equality atoms :  112 (1197 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(t14_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                    = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                  & ( v1_tex_2 @ B @ A ) )
               => ( v1_tex_2 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                    & ( v1_tex_2 @ B @ A ) )
                 => ( v1_tex_2 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( v1_tex_2 @ X25 @ X26 )
      | ( X27
       != ( u1_struct_0 @ X25 ) )
      | ( v1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_tex_2 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 = X28 )
      | ( v1_subset_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('22',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( ( sk_C @ X25 @ X26 )
        = ( u1_struct_0 @ X25 ) )
      | ( v1_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( v1_subset_1 @ ( sk_C @ X25 @ X26 ) @ ( u1_struct_0 @ X26 ) )
      | ( v1_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('31',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','36'])).

thf('38',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','37'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('39',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','36'])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ) )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ) )
    = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['45','65'])).

thf('67',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['66','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['73','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('80',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ C ) )
               => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( u1_struct_0 @ X22 )
       != ( u1_struct_0 @ X24 ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t5_tsep_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( ( u1_struct_0 @ sk_C_1 )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['66','71','72'])).

thf('86',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['66','71','72'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('88',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['86','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('93',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('95',plain,(
    ! [X8: $i] :
      ( ~ ( v1_pre_topc @ X8 )
      | ( X8
        = ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['66','71','72'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('100',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['98','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('105',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('107',plain,
    ( ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['97','105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('109',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( ( u1_struct_0 @ sk_C_1 )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85','107','108','109'])).

thf('111',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ) ),
    inference(eq_res,[status(thm)],['110'])).

thf('112',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('114',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('115',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( ( sk_C @ X25 @ X26 )
        = ( u1_struct_0 @ X25 ) )
      | ( v1_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tex_2 @ X0 @ X0 )
      | ( ( sk_C @ X0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v1_tex_2 @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('120',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_tex_2 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v1_tex_2 @ X0 @ X0 )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tex_2 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tex_2 @ X0 @ X0 )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('124',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('125',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('126',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ X4 @ X4 ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tex_2 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ X0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['117','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ X0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['117','127'])).

thf('130',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ X0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['117','127'])).

thf('132',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( sk_C @ X0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( sk_C @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( sk_C @ X0 @ X0 ) ) )
        = ( sk_C @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( sk_C @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( sk_C @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('142',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('143',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('149',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('150',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('154',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['147','156'])).

thf('158',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( sk_C @ sk_B @ sk_B ) ) )
      = ( sk_C @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','157'])).

thf('159',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('161',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( sk_C @ sk_B @ sk_B ) ) )
    = ( sk_C @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['158','163'])).

thf('165',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) )
      = ( sk_C @ sk_B @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['128','164'])).

thf('166',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('168',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('170',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('171',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['161','162'])).

thf('173',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( sk_C @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['165','171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ X0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['117','127'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( sk_C @ X0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( sk_C @ X0 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['173','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['161','162'])).

thf('180',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( ( u1_struct_0 @ sk_B )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( sk_C @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['165','171','172'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ X0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['117','127'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( sk_C @ X0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( sk_C @ X0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['183','187'])).

thf('189',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['161','162'])).

thf('190',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('192',plain,(
    ! [X8: $i] :
      ( ~ ( v1_pre_topc @ X8 )
      | ( X8
        = ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('193',plain,
    ( ( ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( sk_C @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['165','171','172'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ X0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['117','127'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('197',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( sk_C @ X0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['195','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( sk_C @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( l1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['194','201'])).

thf('203',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['161','162'])).

thf('204',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( sk_C @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['165','171','172'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ X0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['117','127'])).

thf('207',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('208',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( sk_C @ X0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['206','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( sk_C @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['205','211'])).

thf('213',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['161','162'])).

thf('214',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['193','204','214'])).

thf('216',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['161','162'])).

thf('217',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['161','162'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( u1_struct_0 @ sk_B )
       != ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['182','190','215','216','217'])).

thf('219',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(eq_res,[status(thm)],['218'])).

thf('220',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['113','219'])).

thf('221',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['161','162'])).

thf('222',plain,
    ( ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,
    ( ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['112','222'])).

thf('224',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_C_1 )
    | ( ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) )
      = ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','223'])).

thf('225',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) )
      = ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','224'])).

thf('226',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('227',plain,
    ( ( k1_pre_topc @ sk_C_1 @ ( u1_struct_0 @ sk_C_1 ) )
    = ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('229',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['227','228'])).

thf('230',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_B @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('231',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63'])).

thf('232',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','232'])).

thf('234',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ X4 @ X4 ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('235',plain,(
    $false ),
    inference('sup-',[status(thm)],['233','234'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XZineNIhii
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.17/5.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.17/5.38  % Solved by: fo/fo7.sh
% 5.17/5.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.17/5.38  % done 3214 iterations in 4.921s
% 5.17/5.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.17/5.38  % SZS output start Refutation
% 5.17/5.38  thf(sk_A_type, type, sk_A: $i).
% 5.17/5.38  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.17/5.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.17/5.38  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 5.17/5.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.17/5.38  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 5.17/5.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.17/5.38  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 5.17/5.38  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 5.17/5.38  thf(sk_B_type, type, sk_B: $i).
% 5.17/5.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.17/5.38  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 5.17/5.38  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.17/5.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.17/5.38  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.17/5.38  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 5.17/5.38  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 5.17/5.38  thf(t14_tex_2, conjecture,
% 5.17/5.38    (![A:$i]:
% 5.17/5.38     ( ( l1_pre_topc @ A ) =>
% 5.17/5.38       ( ![B:$i]:
% 5.17/5.38         ( ( m1_pre_topc @ B @ A ) =>
% 5.17/5.38           ( ![C:$i]:
% 5.17/5.38             ( ( m1_pre_topc @ C @ A ) =>
% 5.17/5.38               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 5.17/5.38                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 5.17/5.38                   ( v1_tex_2 @ B @ A ) ) =>
% 5.17/5.38                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 5.17/5.38  thf(zf_stmt_0, negated_conjecture,
% 5.17/5.38    (~( ![A:$i]:
% 5.17/5.38        ( ( l1_pre_topc @ A ) =>
% 5.17/5.38          ( ![B:$i]:
% 5.17/5.38            ( ( m1_pre_topc @ B @ A ) =>
% 5.17/5.38              ( ![C:$i]:
% 5.17/5.38                ( ( m1_pre_topc @ C @ A ) =>
% 5.17/5.38                  ( ( ( ( g1_pre_topc @
% 5.17/5.38                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 5.17/5.38                        ( g1_pre_topc @
% 5.17/5.38                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 5.17/5.38                      ( v1_tex_2 @ B @ A ) ) =>
% 5.17/5.38                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 5.17/5.38    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 5.17/5.38  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf(t35_borsuk_1, axiom,
% 5.17/5.38    (![A:$i]:
% 5.17/5.38     ( ( l1_pre_topc @ A ) =>
% 5.17/5.38       ( ![B:$i]:
% 5.17/5.38         ( ( m1_pre_topc @ B @ A ) =>
% 5.17/5.38           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 5.17/5.38  thf('1', plain,
% 5.17/5.38      (![X20 : $i, X21 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X20 @ X21)
% 5.17/5.38          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 5.17/5.38          | ~ (l1_pre_topc @ X21))),
% 5.17/5.38      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 5.17/5.38  thf('2', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_A)
% 5.17/5.38        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['0', '1'])).
% 5.17/5.38  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('4', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 5.17/5.38      inference('demod', [status(thm)], ['2', '3'])).
% 5.17/5.38  thf(t3_subset, axiom,
% 5.17/5.38    (![A:$i,B:$i]:
% 5.17/5.38     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.17/5.38  thf('5', plain,
% 5.17/5.38      (![X5 : $i, X7 : $i]:
% 5.17/5.38         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 5.17/5.38      inference('cnf', [status(esa)], [t3_subset])).
% 5.17/5.38  thf('6', plain,
% 5.17/5.38      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 5.17/5.38        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['4', '5'])).
% 5.17/5.38  thf(d3_tex_2, axiom,
% 5.17/5.38    (![A:$i]:
% 5.17/5.38     ( ( l1_pre_topc @ A ) =>
% 5.17/5.38       ( ![B:$i]:
% 5.17/5.38         ( ( m1_pre_topc @ B @ A ) =>
% 5.17/5.38           ( ( v1_tex_2 @ B @ A ) <=>
% 5.17/5.38             ( ![C:$i]:
% 5.17/5.38               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.17/5.38                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 5.17/5.38                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 5.17/5.38  thf('7', plain,
% 5.17/5.38      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X25 @ X26)
% 5.17/5.38          | ~ (v1_tex_2 @ X25 @ X26)
% 5.17/5.38          | ((X27) != (u1_struct_0 @ X25))
% 5.17/5.38          | (v1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 5.17/5.38          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 5.17/5.38          | ~ (l1_pre_topc @ X26))),
% 5.17/5.38      inference('cnf', [status(esa)], [d3_tex_2])).
% 5.17/5.38  thf('8', plain,
% 5.17/5.38      (![X25 : $i, X26 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X26)
% 5.17/5.38          | ~ (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 5.17/5.38               (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 5.17/5.38          | (v1_subset_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 5.17/5.38          | ~ (v1_tex_2 @ X25 @ X26)
% 5.17/5.38          | ~ (m1_pre_topc @ X25 @ X26))),
% 5.17/5.38      inference('simplify', [status(thm)], ['7'])).
% 5.17/5.38  thf('9', plain,
% 5.17/5.38      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 5.17/5.38        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 5.17/5.38        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_A))),
% 5.17/5.38      inference('sup-', [status(thm)], ['6', '8'])).
% 5.17/5.38  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('11', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('13', plain,
% 5.17/5.38      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 5.17/5.38      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 5.17/5.38  thf('14', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('15', plain,
% 5.17/5.38      (![X20 : $i, X21 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X20 @ X21)
% 5.17/5.38          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 5.17/5.38          | ~ (l1_pre_topc @ X21))),
% 5.17/5.38      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 5.17/5.38  thf('16', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_A)
% 5.17/5.38        | (r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['14', '15'])).
% 5.17/5.38  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('18', plain,
% 5.17/5.38      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 5.17/5.38      inference('demod', [status(thm)], ['16', '17'])).
% 5.17/5.38  thf('19', plain,
% 5.17/5.38      (![X5 : $i, X7 : $i]:
% 5.17/5.38         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 5.17/5.38      inference('cnf', [status(esa)], [t3_subset])).
% 5.17/5.38  thf('20', plain,
% 5.17/5.38      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 5.17/5.38        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['18', '19'])).
% 5.17/5.38  thf(d7_subset_1, axiom,
% 5.17/5.38    (![A:$i,B:$i]:
% 5.17/5.38     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.17/5.38       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 5.17/5.38  thf('21', plain,
% 5.17/5.38      (![X28 : $i, X29 : $i]:
% 5.17/5.38         (((X29) = (X28))
% 5.17/5.38          | (v1_subset_1 @ X29 @ X28)
% 5.17/5.38          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 5.17/5.38      inference('cnf', [status(esa)], [d7_subset_1])).
% 5.17/5.38  thf('22', plain,
% 5.17/5.38      (((v1_subset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 5.17/5.38        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['20', '21'])).
% 5.17/5.38  thf('23', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('24', plain,
% 5.17/5.38      (![X25 : $i, X26 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X25 @ X26)
% 5.17/5.38          | ((sk_C @ X25 @ X26) = (u1_struct_0 @ X25))
% 5.17/5.38          | (v1_tex_2 @ X25 @ X26)
% 5.17/5.38          | ~ (l1_pre_topc @ X26))),
% 5.17/5.38      inference('cnf', [status(esa)], [d3_tex_2])).
% 5.17/5.38  thf('25', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_A)
% 5.17/5.38        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 5.17/5.38        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['23', '24'])).
% 5.17/5.38  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('27', plain,
% 5.17/5.38      (((v1_tex_2 @ sk_C_1 @ sk_A)
% 5.17/5.38        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1)))),
% 5.17/5.38      inference('demod', [status(thm)], ['25', '26'])).
% 5.17/5.38  thf('28', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('29', plain, (((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1))),
% 5.17/5.38      inference('clc', [status(thm)], ['27', '28'])).
% 5.17/5.38  thf('30', plain,
% 5.17/5.38      (![X25 : $i, X26 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X25 @ X26)
% 5.17/5.38          | ~ (v1_subset_1 @ (sk_C @ X25 @ X26) @ (u1_struct_0 @ X26))
% 5.17/5.38          | (v1_tex_2 @ X25 @ X26)
% 5.17/5.38          | ~ (l1_pre_topc @ X26))),
% 5.17/5.38      inference('cnf', [status(esa)], [d3_tex_2])).
% 5.17/5.38  thf('31', plain,
% 5.17/5.38      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_A)
% 5.17/5.38        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 5.17/5.38        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 5.17/5.38      inference('sup-', [status(thm)], ['29', '30'])).
% 5.17/5.38  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('33', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('34', plain,
% 5.17/5.38      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 5.17/5.38        | (v1_tex_2 @ sk_C_1 @ sk_A))),
% 5.17/5.38      inference('demod', [status(thm)], ['31', '32', '33'])).
% 5.17/5.38  thf('35', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('36', plain,
% 5.17/5.38      (~ (v1_subset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 5.17/5.38      inference('clc', [status(thm)], ['34', '35'])).
% 5.17/5.38  thf('37', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 5.17/5.38      inference('clc', [status(thm)], ['22', '36'])).
% 5.17/5.38  thf('38', plain,
% 5.17/5.38      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 5.17/5.38      inference('demod', [status(thm)], ['13', '37'])).
% 5.17/5.38  thf(t2_tsep_1, axiom,
% 5.17/5.38    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 5.17/5.38  thf('39', plain,
% 5.17/5.38      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 5.17/5.38      inference('cnf', [status(esa)], [t2_tsep_1])).
% 5.17/5.38  thf(d10_xboole_0, axiom,
% 5.17/5.38    (![A:$i,B:$i]:
% 5.17/5.38     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.17/5.38  thf('40', plain,
% 5.17/5.38      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.17/5.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.17/5.38  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.17/5.38      inference('simplify', [status(thm)], ['40'])).
% 5.17/5.38  thf('42', plain,
% 5.17/5.38      (![X5 : $i, X7 : $i]:
% 5.17/5.38         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 5.17/5.38      inference('cnf', [status(esa)], [t3_subset])).
% 5.17/5.38  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['41', '42'])).
% 5.17/5.38  thf(t29_pre_topc, axiom,
% 5.17/5.38    (![A:$i]:
% 5.17/5.38     ( ( l1_pre_topc @ A ) =>
% 5.17/5.38       ( ![B:$i]:
% 5.17/5.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.17/5.38           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 5.17/5.38  thf('44', plain,
% 5.17/5.38      (![X13 : $i, X14 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X14 @ X13)) = (X13))
% 5.17/5.38          | ~ (l1_pre_topc @ X14))),
% 5.17/5.38      inference('cnf', [status(esa)], [t29_pre_topc])).
% 5.17/5.38  thf('45', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38              = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['43', '44'])).
% 5.17/5.38  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['41', '42'])).
% 5.17/5.38  thf(dt_k1_pre_topc, axiom,
% 5.17/5.38    (![A:$i,B:$i]:
% 5.17/5.38     ( ( ( l1_pre_topc @ A ) & 
% 5.17/5.38         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.17/5.38       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 5.17/5.38         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 5.17/5.38  thf('47', plain,
% 5.17/5.38      (![X9 : $i, X10 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X9)
% 5.17/5.38          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 5.17/5.38          | (m1_pre_topc @ (k1_pre_topc @ X9 @ X10) @ X9))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 5.17/5.38  thf('48', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['46', '47'])).
% 5.17/5.38  thf('49', plain,
% 5.17/5.38      (![X20 : $i, X21 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X20 @ X21)
% 5.17/5.38          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 5.17/5.38          | ~ (l1_pre_topc @ X21))),
% 5.17/5.38      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 5.17/5.38  thf('50', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | (r1_tarski @ 
% 5.17/5.38             (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 5.17/5.38             (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['48', '49'])).
% 5.17/5.38  thf('51', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((r1_tarski @ 
% 5.17/5.38           (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 5.17/5.38           (u1_struct_0 @ X0))
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('simplify', [status(thm)], ['50'])).
% 5.17/5.38  thf('52', plain,
% 5.17/5.38      (![X5 : $i, X7 : $i]:
% 5.17/5.38         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 5.17/5.38      inference('cnf', [status(esa)], [t3_subset])).
% 5.17/5.38  thf('53', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (m1_subset_1 @ 
% 5.17/5.38             (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 5.17/5.38             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['51', '52'])).
% 5.17/5.38  thf('54', plain, (((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 5.17/5.38      inference('clc', [status(thm)], ['22', '36'])).
% 5.17/5.38  thf('55', plain,
% 5.17/5.38      (![X13 : $i, X14 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X14 @ X13)) = (X13))
% 5.17/5.38          | ~ (l1_pre_topc @ X14))),
% 5.17/5.38      inference('cnf', [status(esa)], [t29_pre_topc])).
% 5.17/5.38  thf('56', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 5.17/5.38          | ~ (l1_pre_topc @ sk_A)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) = (X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['54', '55'])).
% 5.17/5.38  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('58', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) = (X0)))),
% 5.17/5.38      inference('demod', [status(thm)], ['56', '57'])).
% 5.17/5.38  thf('59', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_C_1)
% 5.17/5.38        | ((u1_struct_0 @ 
% 5.17/5.38            (k1_pre_topc @ sk_A @ 
% 5.17/5.38             (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)))))
% 5.17/5.38            = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['53', '58'])).
% 5.17/5.38  thf('60', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf(dt_m1_pre_topc, axiom,
% 5.17/5.38    (![A:$i]:
% 5.17/5.38     ( ( l1_pre_topc @ A ) =>
% 5.17/5.38       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 5.17/5.38  thf('61', plain,
% 5.17/5.38      (![X11 : $i, X12 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X11 @ X12)
% 5.17/5.38          | (l1_pre_topc @ X11)
% 5.17/5.38          | ~ (l1_pre_topc @ X12))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 5.17/5.38  thf('62', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 5.17/5.38      inference('sup-', [status(thm)], ['60', '61'])).
% 5.17/5.38  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('64', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('65', plain,
% 5.17/5.38      (((u1_struct_0 @ 
% 5.17/5.38         (k1_pre_topc @ sk_A @ 
% 5.17/5.38          (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)))))
% 5.17/5.38         = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))))),
% 5.17/5.38      inference('demod', [status(thm)], ['59', '64'])).
% 5.17/5.38  thf('66', plain,
% 5.17/5.38      ((((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 5.17/5.38          = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_C_1))),
% 5.17/5.38      inference('sup+', [status(thm)], ['45', '65'])).
% 5.17/5.38  thf('67', plain,
% 5.17/5.38      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 5.17/5.38        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['18', '19'])).
% 5.17/5.38  thf('68', plain,
% 5.17/5.38      (![X13 : $i, X14 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X14 @ X13)) = (X13))
% 5.17/5.38          | ~ (l1_pre_topc @ X14))),
% 5.17/5.38      inference('cnf', [status(esa)], [t29_pre_topc])).
% 5.17/5.38  thf('69', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_A)
% 5.17/5.38        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 5.17/5.38            = (u1_struct_0 @ sk_C_1)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['67', '68'])).
% 5.17/5.38  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('71', plain,
% 5.17/5.38      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 5.17/5.38         = (u1_struct_0 @ sk_C_1))),
% 5.17/5.38      inference('demod', [status(thm)], ['69', '70'])).
% 5.17/5.38  thf('72', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('73', plain,
% 5.17/5.38      (((u1_struct_0 @ sk_C_1)
% 5.17/5.38         = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))))),
% 5.17/5.38      inference('demod', [status(thm)], ['66', '71', '72'])).
% 5.17/5.38  thf('74', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (m1_subset_1 @ 
% 5.17/5.38             (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 5.17/5.38             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['51', '52'])).
% 5.17/5.38  thf('75', plain,
% 5.17/5.38      (![X9 : $i, X10 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X9)
% 5.17/5.38          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 5.17/5.38          | (m1_pre_topc @ (k1_pre_topc @ X9 @ X10) @ X9))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 5.17/5.38  thf('76', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (m1_pre_topc @ 
% 5.17/5.38             (k1_pre_topc @ X0 @ 
% 5.17/5.38              (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))) @ 
% 5.17/5.38             X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['74', '75'])).
% 5.17/5.38  thf('77', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((m1_pre_topc @ 
% 5.17/5.38           (k1_pre_topc @ X0 @ 
% 5.17/5.38            (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))) @ 
% 5.17/5.38           X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('simplify', [status(thm)], ['76'])).
% 5.17/5.38  thf('78', plain,
% 5.17/5.38      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)) @ sk_C_1)
% 5.17/5.38        | ~ (l1_pre_topc @ sk_C_1))),
% 5.17/5.38      inference('sup+', [status(thm)], ['73', '77'])).
% 5.17/5.38  thf('79', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('80', plain,
% 5.17/5.38      ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)) @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['78', '79'])).
% 5.17/5.38  thf('81', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38              = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['43', '44'])).
% 5.17/5.38  thf(t5_tsep_1, axiom,
% 5.17/5.38    (![A:$i]:
% 5.17/5.38     ( ( l1_pre_topc @ A ) =>
% 5.17/5.38       ( ![B:$i]:
% 5.17/5.38         ( ( m1_pre_topc @ B @ A ) =>
% 5.17/5.38           ( ![C:$i]:
% 5.17/5.38             ( ( m1_pre_topc @ C @ A ) =>
% 5.17/5.38               ( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ C ) ) =>
% 5.17/5.38                 ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 5.17/5.38                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 5.17/5.38  thf('82', plain,
% 5.17/5.38      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X22 @ X23)
% 5.17/5.38          | ((u1_struct_0 @ X22) != (u1_struct_0 @ X24))
% 5.17/5.38          | ((g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22))
% 5.17/5.38              = (g1_pre_topc @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24)))
% 5.17/5.38          | ~ (m1_pre_topc @ X24 @ X23)
% 5.17/5.38          | ~ (l1_pre_topc @ X23))),
% 5.17/5.38      inference('cnf', [status(esa)], [t5_tsep_1])).
% 5.17/5.38  thf('83', plain,
% 5.17/5.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.17/5.38         (((u1_struct_0 @ X0) != (u1_struct_0 @ X1))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X2)
% 5.17/5.38          | ~ (m1_pre_topc @ X1 @ X2)
% 5.17/5.38          | ((g1_pre_topc @ 
% 5.17/5.38              (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 5.17/5.38              (u1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 5.17/5.38              = (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 5.17/5.38          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X2))),
% 5.17/5.38      inference('sup-', [status(thm)], ['81', '82'])).
% 5.17/5.38  thf('84', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (((g1_pre_topc @ 
% 5.17/5.38            (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))) @ 
% 5.17/5.38            (u1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))))
% 5.17/5.38            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.17/5.38          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 5.17/5.38          | ~ (l1_pre_topc @ sk_C_1)
% 5.17/5.38          | ~ (l1_pre_topc @ sk_C_1)
% 5.17/5.38          | ((u1_struct_0 @ sk_C_1) != (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['80', '83'])).
% 5.17/5.38  thf('85', plain,
% 5.17/5.38      (((u1_struct_0 @ sk_C_1)
% 5.17/5.38         = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))))),
% 5.17/5.38      inference('demod', [status(thm)], ['66', '71', '72'])).
% 5.17/5.38  thf('86', plain,
% 5.17/5.38      (((u1_struct_0 @ sk_C_1)
% 5.17/5.38         = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))))),
% 5.17/5.38      inference('demod', [status(thm)], ['66', '71', '72'])).
% 5.17/5.38  thf('87', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((m1_pre_topc @ 
% 5.17/5.38           (k1_pre_topc @ X0 @ 
% 5.17/5.38            (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))) @ 
% 5.17/5.38           X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('simplify', [status(thm)], ['76'])).
% 5.17/5.38  thf('88', plain,
% 5.17/5.38      (![X11 : $i, X12 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X11 @ X12)
% 5.17/5.38          | (l1_pre_topc @ X11)
% 5.17/5.38          | ~ (l1_pre_topc @ X12))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 5.17/5.38  thf('89', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | (l1_pre_topc @ 
% 5.17/5.38             (k1_pre_topc @ X0 @ 
% 5.17/5.38              (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['87', '88'])).
% 5.17/5.38  thf('90', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((l1_pre_topc @ 
% 5.17/5.38           (k1_pre_topc @ X0 @ 
% 5.17/5.38            (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('simplify', [status(thm)], ['89'])).
% 5.17/5.38  thf('91', plain,
% 5.17/5.38      (((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_C_1))),
% 5.17/5.38      inference('sup+', [status(thm)], ['86', '90'])).
% 5.17/5.38  thf('92', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('93', plain,
% 5.17/5.38      ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)))),
% 5.17/5.38      inference('demod', [status(thm)], ['91', '92'])).
% 5.17/5.38  thf('94', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38              = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['43', '44'])).
% 5.17/5.38  thf(abstractness_v1_pre_topc, axiom,
% 5.17/5.38    (![A:$i]:
% 5.17/5.38     ( ( l1_pre_topc @ A ) =>
% 5.17/5.38       ( ( v1_pre_topc @ A ) =>
% 5.17/5.38         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 5.17/5.38  thf('95', plain,
% 5.17/5.38      (![X8 : $i]:
% 5.17/5.38         (~ (v1_pre_topc @ X8)
% 5.17/5.38          | ((X8) = (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 5.17/5.38          | ~ (l1_pre_topc @ X8))),
% 5.17/5.38      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 5.17/5.38  thf('96', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (((k1_pre_topc @ X0 @ (u1_struct_0 @ X0))
% 5.17/5.38            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 5.17/5.38               (u1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 5.17/5.38      inference('sup+', [status(thm)], ['94', '95'])).
% 5.17/5.38  thf('97', plain,
% 5.17/5.38      ((~ (v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_C_1)
% 5.17/5.38        | ((k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))
% 5.17/5.38            = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ 
% 5.17/5.38               (u1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['93', '96'])).
% 5.17/5.38  thf('98', plain,
% 5.17/5.38      (((u1_struct_0 @ sk_C_1)
% 5.17/5.38         = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))))),
% 5.17/5.38      inference('demod', [status(thm)], ['66', '71', '72'])).
% 5.17/5.38  thf('99', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (m1_subset_1 @ 
% 5.17/5.38             (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 5.17/5.38             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['51', '52'])).
% 5.17/5.38  thf('100', plain,
% 5.17/5.38      (![X9 : $i, X10 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X9)
% 5.17/5.38          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 5.17/5.38          | (v1_pre_topc @ (k1_pre_topc @ X9 @ X10)))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 5.17/5.38  thf('101', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (v1_pre_topc @ 
% 5.17/5.38             (k1_pre_topc @ X0 @ 
% 5.17/5.38              (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['99', '100'])).
% 5.17/5.38  thf('102', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((v1_pre_topc @ 
% 5.17/5.38           (k1_pre_topc @ X0 @ 
% 5.17/5.38            (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('simplify', [status(thm)], ['101'])).
% 5.17/5.38  thf('103', plain,
% 5.17/5.38      (((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_C_1))),
% 5.17/5.38      inference('sup+', [status(thm)], ['98', '102'])).
% 5.17/5.38  thf('104', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('105', plain,
% 5.17/5.38      ((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)))),
% 5.17/5.38      inference('demod', [status(thm)], ['103', '104'])).
% 5.17/5.38  thf('106', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('107', plain,
% 5.17/5.38      (((k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))
% 5.17/5.38         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ 
% 5.17/5.38            (u1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1)))))),
% 5.17/5.38      inference('demod', [status(thm)], ['97', '105', '106'])).
% 5.17/5.38  thf('108', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('109', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('110', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (((k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))
% 5.17/5.38            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.17/5.38          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 5.17/5.38          | ((u1_struct_0 @ sk_C_1) != (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('demod', [status(thm)], ['84', '85', '107', '108', '109'])).
% 5.17/5.38  thf('111', plain,
% 5.17/5.38      ((~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 5.17/5.38        | ((k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))
% 5.17/5.38            = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))))),
% 5.17/5.38      inference('eq_res', [status(thm)], ['110'])).
% 5.17/5.38  thf('112', plain,
% 5.17/5.38      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 5.17/5.38         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('113', plain,
% 5.17/5.38      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 5.17/5.38      inference('cnf', [status(esa)], [t2_tsep_1])).
% 5.17/5.38  thf('114', plain,
% 5.17/5.38      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 5.17/5.38      inference('cnf', [status(esa)], [t2_tsep_1])).
% 5.17/5.38  thf('115', plain,
% 5.17/5.38      (![X25 : $i, X26 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X25 @ X26)
% 5.17/5.38          | ((sk_C @ X25 @ X26) = (u1_struct_0 @ X25))
% 5.17/5.38          | (v1_tex_2 @ X25 @ X26)
% 5.17/5.38          | ~ (l1_pre_topc @ X26))),
% 5.17/5.38      inference('cnf', [status(esa)], [d3_tex_2])).
% 5.17/5.38  thf('116', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | (v1_tex_2 @ X0 @ X0)
% 5.17/5.38          | ((sk_C @ X0 @ X0) = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['114', '115'])).
% 5.17/5.38  thf('117', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (((sk_C @ X0 @ X0) = (u1_struct_0 @ X0))
% 5.17/5.38          | (v1_tex_2 @ X0 @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('simplify', [status(thm)], ['116'])).
% 5.17/5.38  thf('118', plain,
% 5.17/5.38      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 5.17/5.38      inference('cnf', [status(esa)], [t2_tsep_1])).
% 5.17/5.38  thf('119', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['41', '42'])).
% 5.17/5.38  thf('120', plain,
% 5.17/5.38      (![X25 : $i, X26 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X26)
% 5.17/5.38          | ~ (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 5.17/5.38               (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 5.17/5.38          | (v1_subset_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 5.17/5.38          | ~ (v1_tex_2 @ X25 @ X26)
% 5.17/5.38          | ~ (m1_pre_topc @ X25 @ X26))),
% 5.17/5.38      inference('simplify', [status(thm)], ['7'])).
% 5.17/5.38  thf('121', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X0 @ X0)
% 5.17/5.38          | ~ (v1_tex_2 @ X0 @ X0)
% 5.17/5.38          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['119', '120'])).
% 5.17/5.38  thf('122', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 5.17/5.38          | ~ (v1_tex_2 @ X0 @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['118', '121'])).
% 5.17/5.38  thf('123', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (v1_tex_2 @ X0 @ X0)
% 5.17/5.38          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('simplify', [status(thm)], ['122'])).
% 5.17/5.38  thf(fc14_subset_1, axiom,
% 5.17/5.38    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 5.17/5.38  thf('124', plain, (![X4 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X4) @ X4)),
% 5.17/5.38      inference('cnf', [status(esa)], [fc14_subset_1])).
% 5.17/5.38  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.17/5.38  thf('125', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 5.17/5.38      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.17/5.38  thf('126', plain, (![X4 : $i]: ~ (v1_subset_1 @ X4 @ X4)),
% 5.17/5.38      inference('demod', [status(thm)], ['124', '125'])).
% 5.17/5.38  thf('127', plain,
% 5.17/5.38      (![X0 : $i]: (~ (l1_pre_topc @ X0) | ~ (v1_tex_2 @ X0 @ X0))),
% 5.17/5.38      inference('clc', [status(thm)], ['123', '126'])).
% 5.17/5.38  thf('128', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0) | ((sk_C @ X0 @ X0) = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('clc', [status(thm)], ['117', '127'])).
% 5.17/5.38  thf('129', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0) | ((sk_C @ X0 @ X0) = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('clc', [status(thm)], ['117', '127'])).
% 5.17/5.38  thf('130', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['41', '42'])).
% 5.17/5.38  thf('131', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0) | ((sk_C @ X0 @ X0) = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('clc', [status(thm)], ['117', '127'])).
% 5.17/5.38  thf('132', plain,
% 5.17/5.38      (![X13 : $i, X14 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X14 @ X13)) = (X13))
% 5.17/5.38          | ~ (l1_pre_topc @ X14))),
% 5.17/5.38      inference('cnf', [status(esa)], [t29_pre_topc])).
% 5.17/5.38  thf('133', plain,
% 5.17/5.38      (![X0 : $i, X1 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (sk_C @ X0 @ X0)))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['131', '132'])).
% 5.17/5.38  thf('134', plain,
% 5.17/5.38      (![X0 : $i, X1 : $i]:
% 5.17/5.38         (((u1_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (sk_C @ X0 @ X0))))),
% 5.17/5.38      inference('simplify', [status(thm)], ['133'])).
% 5.17/5.38  thf('135', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (sk_C @ X0 @ X0)))
% 5.17/5.38              = (sk_C @ X0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['130', '134'])).
% 5.17/5.38  thf('136', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38            = (sk_C @ X0 @ X0))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup+', [status(thm)], ['129', '135'])).
% 5.17/5.38  thf('137', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38              = (sk_C @ X0 @ X0)))),
% 5.17/5.38      inference('simplify', [status(thm)], ['136'])).
% 5.17/5.38  thf('138', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (m1_subset_1 @ 
% 5.17/5.38             (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 5.17/5.38             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['51', '52'])).
% 5.17/5.38  thf('139', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((m1_subset_1 @ (sk_C @ X0 @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup+', [status(thm)], ['137', '138'])).
% 5.17/5.38  thf('140', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (m1_subset_1 @ (sk_C @ X0 @ X0) @ 
% 5.17/5.38             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 5.17/5.38      inference('simplify', [status(thm)], ['139'])).
% 5.17/5.38  thf('141', plain,
% 5.17/5.38      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 5.17/5.38        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['4', '5'])).
% 5.17/5.38  thf('142', plain,
% 5.17/5.38      (![X13 : $i, X14 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X14 @ X13)) = (X13))
% 5.17/5.38          | ~ (l1_pre_topc @ X14))),
% 5.17/5.38      inference('cnf', [status(esa)], [t29_pre_topc])).
% 5.17/5.38  thf('143', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_A)
% 5.17/5.38        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 5.17/5.38            = (u1_struct_0 @ sk_B)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['141', '142'])).
% 5.17/5.38  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('145', plain,
% 5.17/5.38      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 5.17/5.38         = (u1_struct_0 @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['143', '144'])).
% 5.17/5.38  thf('146', plain,
% 5.17/5.38      (![X13 : $i, X14 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X14 @ X13)) = (X13))
% 5.17/5.38          | ~ (l1_pre_topc @ X14))),
% 5.17/5.38      inference('cnf', [status(esa)], [t29_pre_topc])).
% 5.17/5.38  thf('147', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 5.17/5.38          | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 5.17/5.38          | ((u1_struct_0 @ 
% 5.17/5.38              (k1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ X0))
% 5.17/5.38              = (X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['145', '146'])).
% 5.17/5.38  thf('148', plain,
% 5.17/5.38      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 5.17/5.38        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['4', '5'])).
% 5.17/5.38  thf('149', plain,
% 5.17/5.38      (![X9 : $i, X10 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X9)
% 5.17/5.38          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 5.17/5.38          | (m1_pre_topc @ (k1_pre_topc @ X9 @ X10) @ X9))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 5.17/5.38  thf('150', plain,
% 5.17/5.38      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)
% 5.17/5.38        | ~ (l1_pre_topc @ sk_A))),
% 5.17/5.38      inference('sup-', [status(thm)], ['148', '149'])).
% 5.17/5.38  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('152', plain,
% 5.17/5.38      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)),
% 5.17/5.38      inference('demod', [status(thm)], ['150', '151'])).
% 5.17/5.38  thf('153', plain,
% 5.17/5.38      (![X11 : $i, X12 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X11 @ X12)
% 5.17/5.38          | (l1_pre_topc @ X11)
% 5.17/5.38          | ~ (l1_pre_topc @ X12))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 5.17/5.38  thf('154', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_A)
% 5.17/5.38        | (l1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['152', '153'])).
% 5.17/5.38  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('156', plain,
% 5.17/5.38      ((l1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))),
% 5.17/5.38      inference('demod', [status(thm)], ['154', '155'])).
% 5.17/5.38  thf('157', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 5.17/5.38          | ((u1_struct_0 @ 
% 5.17/5.38              (k1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ X0))
% 5.17/5.38              = (X0)))),
% 5.17/5.38      inference('demod', [status(thm)], ['147', '156'])).
% 5.17/5.38  thf('158', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_B)
% 5.17/5.38        | ((u1_struct_0 @ 
% 5.17/5.38            (k1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 5.17/5.38             (sk_C @ sk_B @ sk_B)))
% 5.17/5.38            = (sk_C @ sk_B @ sk_B)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['140', '157'])).
% 5.17/5.38  thf('159', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('160', plain,
% 5.17/5.38      (![X11 : $i, X12 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X11 @ X12)
% 5.17/5.38          | (l1_pre_topc @ X11)
% 5.17/5.38          | ~ (l1_pre_topc @ X12))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 5.17/5.38  thf('161', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 5.17/5.38      inference('sup-', [status(thm)], ['159', '160'])).
% 5.17/5.38  thf('162', plain, ((l1_pre_topc @ sk_A)),
% 5.17/5.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.17/5.38  thf('163', plain, ((l1_pre_topc @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['161', '162'])).
% 5.17/5.38  thf('164', plain,
% 5.17/5.38      (((u1_struct_0 @ 
% 5.17/5.38         (k1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 5.17/5.38          (sk_C @ sk_B @ sk_B)))
% 5.17/5.38         = (sk_C @ sk_B @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['158', '163'])).
% 5.17/5.38  thf('165', plain,
% 5.17/5.38      ((((u1_struct_0 @ 
% 5.17/5.38          (k1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 5.17/5.38           (u1_struct_0 @ sk_B)))
% 5.17/5.38          = (sk_C @ sk_B @ sk_B))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_B))),
% 5.17/5.38      inference('sup+', [status(thm)], ['128', '164'])).
% 5.17/5.38  thf('166', plain,
% 5.17/5.38      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 5.17/5.38         = (u1_struct_0 @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['143', '144'])).
% 5.17/5.38  thf('167', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38              = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['43', '44'])).
% 5.17/5.38  thf('168', plain,
% 5.17/5.38      ((((u1_struct_0 @ 
% 5.17/5.38          (k1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 5.17/5.38           (u1_struct_0 @ sk_B)))
% 5.17/5.38          = (u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B))))
% 5.17/5.38        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B))))),
% 5.17/5.38      inference('sup+', [status(thm)], ['166', '167'])).
% 5.17/5.38  thf('169', plain,
% 5.17/5.38      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 5.17/5.38         = (u1_struct_0 @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['143', '144'])).
% 5.17/5.38  thf('170', plain,
% 5.17/5.38      ((l1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))),
% 5.17/5.38      inference('demod', [status(thm)], ['154', '155'])).
% 5.17/5.38  thf('171', plain,
% 5.17/5.38      (((u1_struct_0 @ 
% 5.17/5.38         (k1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 5.17/5.38          (u1_struct_0 @ sk_B)))
% 5.17/5.38         = (u1_struct_0 @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['168', '169', '170'])).
% 5.17/5.38  thf('172', plain, ((l1_pre_topc @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['161', '162'])).
% 5.17/5.38  thf('173', plain, (((u1_struct_0 @ sk_B) = (sk_C @ sk_B @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['165', '171', '172'])).
% 5.17/5.38  thf('174', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0) | ((sk_C @ X0 @ X0) = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('clc', [status(thm)], ['117', '127'])).
% 5.17/5.38  thf('175', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['46', '47'])).
% 5.17/5.38  thf('176', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (sk_C @ X0 @ X0)) @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup+', [status(thm)], ['174', '175'])).
% 5.17/5.38  thf('177', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (sk_C @ X0 @ X0)) @ X0))),
% 5.17/5.38      inference('simplify', [status(thm)], ['176'])).
% 5.17/5.38  thf('178', plain,
% 5.17/5.38      (((m1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)) @ sk_B)
% 5.17/5.38        | ~ (l1_pre_topc @ sk_B))),
% 5.17/5.38      inference('sup+', [status(thm)], ['173', '177'])).
% 5.17/5.38  thf('179', plain, ((l1_pre_topc @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['161', '162'])).
% 5.17/5.38  thf('180', plain,
% 5.17/5.38      ((m1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)) @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['178', '179'])).
% 5.17/5.38  thf('181', plain,
% 5.17/5.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.17/5.38         (((u1_struct_0 @ X0) != (u1_struct_0 @ X1))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X2)
% 5.17/5.38          | ~ (m1_pre_topc @ X1 @ X2)
% 5.17/5.38          | ((g1_pre_topc @ 
% 5.17/5.38              (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 5.17/5.38              (u1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 5.17/5.38              = (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 5.17/5.38          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X2))),
% 5.17/5.38      inference('sup-', [status(thm)], ['81', '82'])).
% 5.17/5.38  thf('182', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (((g1_pre_topc @ 
% 5.17/5.38            (u1_struct_0 @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))) @ 
% 5.17/5.38            (u1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))))
% 5.17/5.38            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.17/5.38          | ~ (m1_pre_topc @ X0 @ sk_B)
% 5.17/5.38          | ~ (l1_pre_topc @ sk_B)
% 5.17/5.38          | ~ (l1_pre_topc @ sk_B)
% 5.17/5.38          | ((u1_struct_0 @ sk_B) != (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['180', '181'])).
% 5.17/5.38  thf('183', plain, (((u1_struct_0 @ sk_B) = (sk_C @ sk_B @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['165', '171', '172'])).
% 5.17/5.38  thf('184', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0) | ((sk_C @ X0 @ X0) = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('clc', [status(thm)], ['117', '127'])).
% 5.17/5.38  thf('185', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38              = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['43', '44'])).
% 5.17/5.38  thf('186', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (((u1_struct_0 @ (k1_pre_topc @ X0 @ (sk_C @ X0 @ X0)))
% 5.17/5.38            = (u1_struct_0 @ X0))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup+', [status(thm)], ['184', '185'])).
% 5.17/5.38  thf('187', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (sk_C @ X0 @ X0)))
% 5.17/5.38              = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('simplify', [status(thm)], ['186'])).
% 5.17/5.38  thf('188', plain,
% 5.17/5.38      ((((u1_struct_0 @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))
% 5.17/5.38          = (u1_struct_0 @ sk_B))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_B))),
% 5.17/5.38      inference('sup+', [status(thm)], ['183', '187'])).
% 5.17/5.38  thf('189', plain, ((l1_pre_topc @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['161', '162'])).
% 5.17/5.38  thf('190', plain,
% 5.17/5.38      (((u1_struct_0 @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))
% 5.17/5.38         = (u1_struct_0 @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['188', '189'])).
% 5.17/5.38  thf('191', plain,
% 5.17/5.38      (((u1_struct_0 @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))
% 5.17/5.38         = (u1_struct_0 @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['188', '189'])).
% 5.17/5.38  thf('192', plain,
% 5.17/5.38      (![X8 : $i]:
% 5.17/5.38         (~ (v1_pre_topc @ X8)
% 5.17/5.38          | ((X8) = (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 5.17/5.38          | ~ (l1_pre_topc @ X8))),
% 5.17/5.38      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 5.17/5.38  thf('193', plain,
% 5.17/5.38      ((((k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))
% 5.17/5.38          = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ 
% 5.17/5.38             (u1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))))
% 5.17/5.38        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))
% 5.17/5.38        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))))),
% 5.17/5.38      inference('sup+', [status(thm)], ['191', '192'])).
% 5.17/5.38  thf('194', plain, (((u1_struct_0 @ sk_B) = (sk_C @ sk_B @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['165', '171', '172'])).
% 5.17/5.38  thf('195', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0) | ((sk_C @ X0 @ X0) = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('clc', [status(thm)], ['117', '127'])).
% 5.17/5.38  thf('196', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['46', '47'])).
% 5.17/5.38  thf('197', plain,
% 5.17/5.38      (![X11 : $i, X12 : $i]:
% 5.17/5.38         (~ (m1_pre_topc @ X11 @ X12)
% 5.17/5.38          | (l1_pre_topc @ X11)
% 5.17/5.38          | ~ (l1_pre_topc @ X12))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 5.17/5.38  thf('198', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['196', '197'])).
% 5.17/5.38  thf('199', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('simplify', [status(thm)], ['198'])).
% 5.17/5.38  thf('200', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (sk_C @ X0 @ X0)))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup+', [status(thm)], ['195', '199'])).
% 5.17/5.38  thf('201', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (l1_pre_topc @ (k1_pre_topc @ X0 @ (sk_C @ X0 @ X0))))),
% 5.17/5.38      inference('simplify', [status(thm)], ['200'])).
% 5.17/5.38  thf('202', plain,
% 5.17/5.38      (((l1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_B))),
% 5.17/5.38      inference('sup+', [status(thm)], ['194', '201'])).
% 5.17/5.38  thf('203', plain, ((l1_pre_topc @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['161', '162'])).
% 5.17/5.38  thf('204', plain,
% 5.17/5.38      ((l1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))),
% 5.17/5.38      inference('demod', [status(thm)], ['202', '203'])).
% 5.17/5.38  thf('205', plain, (((u1_struct_0 @ sk_B) = (sk_C @ sk_B @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['165', '171', '172'])).
% 5.17/5.38  thf('206', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0) | ((sk_C @ X0 @ X0) = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('clc', [status(thm)], ['117', '127'])).
% 5.17/5.38  thf('207', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['41', '42'])).
% 5.17/5.38  thf('208', plain,
% 5.17/5.38      (![X9 : $i, X10 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X9)
% 5.17/5.38          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 5.17/5.38          | (v1_pre_topc @ (k1_pre_topc @ X9 @ X10)))),
% 5.17/5.38      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 5.17/5.38  thf('209', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup-', [status(thm)], ['207', '208'])).
% 5.17/5.38  thf('210', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         ((v1_pre_topc @ (k1_pre_topc @ X0 @ (sk_C @ X0 @ X0)))
% 5.17/5.38          | ~ (l1_pre_topc @ X0)
% 5.17/5.38          | ~ (l1_pre_topc @ X0))),
% 5.17/5.38      inference('sup+', [status(thm)], ['206', '209'])).
% 5.17/5.38  thf('211', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | (v1_pre_topc @ (k1_pre_topc @ X0 @ (sk_C @ X0 @ X0))))),
% 5.17/5.38      inference('simplify', [status(thm)], ['210'])).
% 5.17/5.38  thf('212', plain,
% 5.17/5.38      (((v1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_B))),
% 5.17/5.38      inference('sup+', [status(thm)], ['205', '211'])).
% 5.17/5.38  thf('213', plain, ((l1_pre_topc @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['161', '162'])).
% 5.17/5.38  thf('214', plain,
% 5.17/5.38      ((v1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))),
% 5.17/5.38      inference('demod', [status(thm)], ['212', '213'])).
% 5.17/5.38  thf('215', plain,
% 5.17/5.38      (((k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))
% 5.17/5.38         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ 
% 5.17/5.38            (u1_pre_topc @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))))),
% 5.17/5.38      inference('demod', [status(thm)], ['193', '204', '214'])).
% 5.17/5.38  thf('216', plain, ((l1_pre_topc @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['161', '162'])).
% 5.17/5.38  thf('217', plain, ((l1_pre_topc @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['161', '162'])).
% 5.17/5.38  thf('218', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (((k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))
% 5.17/5.38            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.17/5.38          | ~ (m1_pre_topc @ X0 @ sk_B)
% 5.17/5.38          | ((u1_struct_0 @ sk_B) != (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('demod', [status(thm)], ['182', '190', '215', '216', '217'])).
% 5.17/5.38  thf('219', plain,
% 5.17/5.38      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 5.17/5.38        | ((k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))
% 5.17/5.38            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 5.17/5.38      inference('eq_res', [status(thm)], ['218'])).
% 5.17/5.38  thf('220', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_B)
% 5.17/5.38        | ((k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))
% 5.17/5.38            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['113', '219'])).
% 5.17/5.38  thf('221', plain, ((l1_pre_topc @ sk_B)),
% 5.17/5.38      inference('demod', [status(thm)], ['161', '162'])).
% 5.17/5.38  thf('222', plain,
% 5.17/5.38      (((k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))
% 5.17/5.38         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 5.17/5.38      inference('demod', [status(thm)], ['220', '221'])).
% 5.17/5.38  thf('223', plain,
% 5.17/5.38      (((k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))
% 5.17/5.38         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 5.17/5.38      inference('demod', [status(thm)], ['112', '222'])).
% 5.17/5.38  thf('224', plain,
% 5.17/5.38      ((~ (m1_pre_topc @ sk_C_1 @ sk_C_1)
% 5.17/5.38        | ((k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))
% 5.17/5.38            = (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))))),
% 5.17/5.38      inference('demod', [status(thm)], ['111', '223'])).
% 5.17/5.38  thf('225', plain,
% 5.17/5.38      ((~ (l1_pre_topc @ sk_C_1)
% 5.17/5.38        | ((k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))
% 5.17/5.38            = (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B))))),
% 5.17/5.38      inference('sup-', [status(thm)], ['39', '224'])).
% 5.17/5.38  thf('226', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('227', plain,
% 5.17/5.38      (((k1_pre_topc @ sk_C_1 @ (u1_struct_0 @ sk_C_1))
% 5.17/5.38         = (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))),
% 5.17/5.38      inference('demod', [status(thm)], ['225', '226'])).
% 5.17/5.38  thf('228', plain,
% 5.17/5.38      (![X0 : $i]:
% 5.17/5.38         (~ (l1_pre_topc @ X0)
% 5.17/5.38          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 5.17/5.38              = (u1_struct_0 @ X0)))),
% 5.17/5.38      inference('sup-', [status(thm)], ['43', '44'])).
% 5.17/5.38  thf('229', plain,
% 5.17/5.38      ((((u1_struct_0 @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))
% 5.17/5.38          = (u1_struct_0 @ sk_C_1))
% 5.17/5.38        | ~ (l1_pre_topc @ sk_C_1))),
% 5.17/5.38      inference('sup+', [status(thm)], ['227', '228'])).
% 5.17/5.38  thf('230', plain,
% 5.17/5.38      (((u1_struct_0 @ (k1_pre_topc @ sk_B @ (u1_struct_0 @ sk_B)))
% 5.17/5.38         = (u1_struct_0 @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['188', '189'])).
% 5.17/5.38  thf('231', plain, ((l1_pre_topc @ sk_C_1)),
% 5.17/5.38      inference('demod', [status(thm)], ['62', '63'])).
% 5.17/5.38  thf('232', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 5.17/5.38      inference('demod', [status(thm)], ['229', '230', '231'])).
% 5.17/5.38  thf('233', plain,
% 5.17/5.38      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 5.17/5.38      inference('demod', [status(thm)], ['38', '232'])).
% 5.17/5.38  thf('234', plain, (![X4 : $i]: ~ (v1_subset_1 @ X4 @ X4)),
% 5.17/5.38      inference('demod', [status(thm)], ['124', '125'])).
% 5.17/5.38  thf('235', plain, ($false), inference('sup-', [status(thm)], ['233', '234'])).
% 5.17/5.38  
% 5.17/5.38  % SZS output end Refutation
% 5.17/5.38  
% 5.17/5.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
