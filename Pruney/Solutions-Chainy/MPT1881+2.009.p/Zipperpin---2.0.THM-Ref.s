%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jLEbaDqayq

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 247 expanded)
%              Number of leaves         :   28 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          : 1090 (2803 expanded)
%              Number of equality atoms :   36 (  61 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('8',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_tex_2 @ X17 @ X18 )
      | ~ ( v2_tex_2 @ X19 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( X17 = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B = X0 )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','24'])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v3_tex_2 @ sk_B @ sk_A )
      & ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('35',plain,(
    ! [X11: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('36',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ! [X11: $i] :
      ~ ( v1_subset_1 @ X11 @ X11 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( v1_subset_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('42',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('44',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('46',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( m1_subset_1 @ ( sk_C_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('56',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( r1_tarski @ X17 @ ( sk_C_1 @ X17 @ X18 ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('70',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('71',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('72',plain,
    ( ( ( v3_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70','71'])).

thf('73',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( ( ( sk_C_1 @ sk_B @ sk_A )
        = sk_B )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = sk_B ) )
   <= ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_A )
      = sk_B )
   <= ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( X17
       != ( sk_C_1 @ X17 @ X18 ) )
      | ( v3_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','91'])).

thf('93',plain,
    ( ( ( sk_B != sk_B )
      | ( v3_tex_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','92'])).

thf('94',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
   <= ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ~ ( v3_tex_2 @ sk_B @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jLEbaDqayq
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 141 iterations in 0.057s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(t49_tex_2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.51             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51              ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.51                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.20/0.51       ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(dt_k2_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.51  thf('3', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.51  thf('4', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t43_tex_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.51          | (v2_tex_2 @ X20 @ X21)
% 0.20/0.51          | ~ (l1_pre_topc @ X21)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X21)
% 0.20/0.51          | ~ (v2_pre_topc @ X21)
% 0.20/0.51          | (v2_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain, (((v3_tex_2 @ sk_B @ sk_A)) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d7_tex_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.51             ( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.51               ( ![C:$i]:
% 0.20/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.51                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | ~ (v3_tex_2 @ X17 @ X18)
% 0.20/0.51          | ~ (v2_tex_2 @ X19 @ X18)
% 0.20/0.51          | ~ (r1_tarski @ X17 @ X19)
% 0.20/0.51          | ((X17) = (X19))
% 0.20/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | ~ (l1_pre_topc @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ((sk_B) = (X0))
% 0.20/0.51          | ~ (r1_tarski @ sk_B @ X0)
% 0.20/0.51          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ((sk_B) = (X0))
% 0.20/0.51          | ~ (r1_tarski @ sk_B @ X0)
% 0.20/0.51          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.51          | ~ (v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.51           | ~ (r1_tarski @ sk_B @ X0)
% 0.20/0.51           | ((sk_B) = (X0))
% 0.20/0.51           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.51         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.20/0.51         | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.20/0.51         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t2_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         ((r2_hidden @ X12 @ X13)
% 0.20/0.51          | (v1_xboole_0 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf(fc1_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('20', plain, (![X10 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.51  thf('21', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf(d1_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.51          | (r1_tarski @ X6 @ X4)
% 0.20/0.51          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X4 : $i, X6 : $i]:
% 0.20/0.51         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.51  thf('24', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.20/0.51         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 0.20/0.51         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.51         | ~ (v1_tdlat_3 @ sk_A)
% 0.20/0.51         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51         | (v2_struct_0 @ sk_A)
% 0.20/0.51         | ((sk_B) = (u1_struct_0 @ sk_A)))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '25'])).
% 0.20/0.51  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_A) | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.20/0.51  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((sk_B) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (((v1_subset_1 @ sk_B @ sk_B))
% 0.20/0.51         <= (((v3_tex_2 @ sk_B @ sk_A)) & 
% 0.20/0.51             ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf(fc14_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.20/0.51  thf('35', plain, (![X11 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X11) @ X11)),
% 0.20/0.51      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.20/0.51  thf('36', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.51  thf('37', plain, (![X11 : $i]: ~ (v1_subset_1 @ X11 @ X11)),
% 0.20/0.51      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.20/0.51       ~ ((v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.20/0.51       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d7_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (((X16) = (X15))
% 0.20/0.51          | (v1_subset_1 @ X16 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('46', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | ~ (v2_tex_2 @ X17 @ X18)
% 0.20/0.51          | (m1_subset_1 @ (sk_C_1 @ X17 @ X18) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | (v3_tex_2 @ X17 @ X18)
% 0.20/0.51          | ~ (l1_pre_topc @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | (m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | (m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | (m1_subset_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         ((r2_hidden @ X12 @ X13)
% 0.20/0.51          | (v1_xboole_0 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (r2_hidden @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X4 : $i, X6 : $i]:
% 0.20/0.51         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (r1_tarski @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.20/0.51             (u1_struct_0 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('56', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | ~ (v2_tex_2 @ X17 @ X18)
% 0.20/0.51          | (r1_tarski @ X17 @ (sk_C_1 @ X17 @ X18))
% 0.20/0.51          | (v3_tex_2 @ X17 @ X18)
% 0.20/0.51          | ~ (l1_pre_topc @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.20/0.51             (sk_C_1 @ (u1_struct_0 @ X0) @ X0))
% 0.20/0.51          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.20/0.51             (sk_C_1 @ (u1_struct_0 @ X0) @ X0))
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['55', '58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.20/0.51             (sk_C_1 @ (u1_struct_0 @ X0) @ X0))
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | ~ (r1_tarski @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ 
% 0.20/0.51               (u1_struct_0 @ X0))
% 0.20/0.51          | ((sk_C_1 @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ((sk_C_1 @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '62'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_C_1 @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 0.20/0.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.51         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51         | ~ (v1_tdlat_3 @ sk_A)
% 0.20/0.51         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51         | (v2_struct_0 @ sk_A)
% 0.20/0.51         | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         | ((sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_A) = (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['44', '64'])).
% 0.20/0.51  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      ((((v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.51         | (v2_struct_0 @ sk_A)
% 0.20/0.51         | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.51         | ((sk_C_1 @ sk_B @ sk_A) = (sk_B))))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['65', '66', '67', '68', '69', '70', '71'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (((((sk_C_1 @ sk_B @ sk_A) = (sk_B))
% 0.20/0.51         | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.20/0.51             ~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.51  thf('75', plain, (![X10 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_A) | ((sk_C_1 @ sk_B @ sk_A) = (sk_B))))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.20/0.51             ~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.51  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      ((((sk_C_1 @ sk_B @ sk_A) = (sk_B)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.20/0.51             ~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['76', '77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | ~ (v2_tex_2 @ X17 @ X18)
% 0.20/0.51          | ((X17) != (sk_C_1 @ X17 @ X18))
% 0.20/0.51          | (v3_tex_2 @ X17 @ X18)
% 0.20/0.51          | ~ (l1_pre_topc @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (v3_tex_2 @ sk_B @ sk_A)
% 0.20/0.51        | ((sk_B) != (sk_C_1 @ sk_B @ sk_A))
% 0.20/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.51  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.51          | (v2_tex_2 @ X20 @ X21)
% 0.20/0.51          | ~ (l1_pre_topc @ X21)
% 0.20/0.51          | ~ (v1_tdlat_3 @ X21)
% 0.20/0.51          | ~ (v2_pre_topc @ X21)
% 0.20/0.51          | (v2_struct_0 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v1_tdlat_3 @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.51  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('87', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('89', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.20/0.51  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('91', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C_1 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['81', '82', '91'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (((((sk_B) != (sk_B)) | (v3_tex_2 @ sk_B @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.20/0.51             ~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['78', '92'])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (((v3_tex_2 @ sk_B @ sk_A))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.20/0.51             ~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['93'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      ((~ (v3_tex_2 @ sk_B @ sk_A)) <= (~ ((v3_tex_2 @ sk_B @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) | 
% 0.20/0.51       ((v3_tex_2 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.51  thf('97', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '96'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
