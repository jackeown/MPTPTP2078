%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mrnueYMdAB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:58 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  202 (1627 expanded)
%              Number of leaves         :   41 ( 458 expanded)
%              Depth                    :   32
%              Number of atoms          : 1435 (20122 expanded)
%              Number of equality atoms :   24 ( 244 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X29 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v1_zfmisc_1 @ X27 )
      | ( X28 = X27 )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X25 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( X25
        = ( u1_struct_0 @ ( sk_C @ X25 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('54',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','51','52','53'])).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','51','52','53'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X32 ) @ X31 ) @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X25 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('90',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('92',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','90','91'])).

thf('93',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ( m1_pre_topc @ ( sk_C_1 @ X29 @ X30 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','92'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['108','109'])).

thf(cc32_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('111',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ( v7_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('117',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X29 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','122'])).

thf('124',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','90','91'])).

thf('129',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ( X29
        = ( u1_struct_0 @ ( sk_C_1 @ X29 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','92'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('144',plain,(
    ! [X14: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ~ ( v7_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('145',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('147',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','90'])).

thf('148',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['145','148'])).

thf('150',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['108','109'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('151',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('152',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('155',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('156',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['149','156'])).

thf('158',plain,(
    v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['132','157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['98','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mrnueYMdAB
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:45:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 178 iterations in 0.128s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.36/0.58  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.36/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.58  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.36/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.58  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.36/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.58  thf(t44_tex_2, conjecture,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.36/0.58         ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.58           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i]:
% 0.36/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.58            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58          ( ![B:$i]:
% 0.36/0.58            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.59                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.59              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t34_tex_2, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.59             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.59           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.36/0.59                ( ![C:$i]:
% 0.36/0.59                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.36/0.59                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.59                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      (![X29 : $i, X30 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X29)
% 0.36/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.36/0.59          | ~ (v2_tex_2 @ X29 @ X30)
% 0.36/0.59          | ~ (v2_struct_0 @ (sk_C_1 @ X29 @ X30))
% 0.36/0.59          | ~ (l1_pre_topc @ X30)
% 0.36/0.59          | ~ (v2_pre_topc @ X30)
% 0.36/0.59          | (v2_struct_0 @ X30))),
% 0.36/0.59      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.59  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.36/0.59  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('split', [status(esa)], ['6'])).
% 0.36/0.59  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('split', [status(esa)], ['8'])).
% 0.36/0.59  thf('10', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.59      inference('split', [status(esa)], ['6'])).
% 0.36/0.59  thf(d1_xboole_0, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.59  thf(t1_subset, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.36/0.59      inference('cnf', [status(esa)], [t1_subset])).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.59  thf(redefinition_k6_domain_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.59       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      (![X20 : $i, X21 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X20)
% 0.36/0.59          | ~ (m1_subset_1 @ X21 @ X20)
% 0.36/0.59          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X0)
% 0.36/0.59          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.36/0.59          | (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.36/0.59          | (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.59  thf(dt_k6_domain_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.59       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      (![X18 : $i, X19 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X18)
% 0.36/0.59          | ~ (m1_subset_1 @ X19 @ X18)
% 0.36/0.59          | (m1_subset_1 @ (k6_domain_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18)))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X0)
% 0.36/0.59          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 0.36/0.59             (k1_zfmisc_1 @ X0))
% 0.36/0.59          | (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.36/0.59          | (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.59  thf(t3_subset, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      (![X8 : $i, X9 : $i]:
% 0.36/0.59         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X0)
% 0.36/0.59          | (r1_tarski @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 0.36/0.59          | (v1_xboole_0 @ X0)
% 0.36/0.59          | (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['16', '22'])).
% 0.36/0.59  thf('24', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['23'])).
% 0.36/0.59  thf(t1_tex_2, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.36/0.59           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      (![X27 : $i, X28 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X27)
% 0.36/0.59          | ~ (v1_zfmisc_1 @ X27)
% 0.36/0.59          | ((X28) = (X27))
% 0.36/0.59          | ~ (r1_tarski @ X28 @ X27)
% 0.36/0.59          | (v1_xboole_0 @ X28))),
% 0.36/0.59      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X0)
% 0.36/0.59          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.36/0.59          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.36/0.59          | ~ (v1_zfmisc_1 @ X0)
% 0.36/0.59          | (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_zfmisc_1 @ X0)
% 0.36/0.59          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.36/0.59          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.36/0.59          | (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.59  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.36/0.59  thf('28', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X0)
% 0.36/0.59          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.36/0.59          | ~ (v1_zfmisc_1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t10_tsep_1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.59             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.59           ( ?[C:$i]:
% 0.36/0.59             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.36/0.59               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (![X25 : $i, X26 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X25)
% 0.36/0.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.59          | (m1_pre_topc @ (sk_C @ X25 @ X26) @ X26)
% 0.36/0.59          | ~ (l1_pre_topc @ X26)
% 0.36/0.59          | (v2_struct_0 @ X26))),
% 0.36/0.59      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.59  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.59  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['34', '35'])).
% 0.36/0.59  thf('37', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('38', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['36', '37'])).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.59  thf(t55_pre_topc, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.59           ( ![C:$i]:
% 0.36/0.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.59               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.59         ((v2_struct_0 @ X15)
% 0.36/0.59          | ~ (m1_pre_topc @ X15 @ X16)
% 0.36/0.59          | (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.36/0.59          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.36/0.59          | ~ (l1_pre_topc @ X16)
% 0.36/0.59          | (v2_struct_0 @ X16))),
% 0.36/0.59      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.36/0.59  thf('41', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.36/0.59          | (v2_struct_0 @ X1)
% 0.36/0.59          | ~ (l1_pre_topc @ X1)
% 0.36/0.59          | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ X0)) @ (u1_struct_0 @ X1))
% 0.36/0.59          | ~ (m1_pre_topc @ X0 @ X1)
% 0.36/0.59          | (v2_struct_0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.59  thf('42', plain,
% 0.36/0.59      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.36/0.59           (u1_struct_0 @ sk_A))
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['38', '41'])).
% 0.36/0.59  thf('43', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('44', plain,
% 0.36/0.59      (![X25 : $i, X26 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X25)
% 0.36/0.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.59          | ((X25) = (u1_struct_0 @ (sk_C @ X25 @ X26)))
% 0.36/0.59          | ~ (l1_pre_topc @ X26)
% 0.36/0.59          | (v2_struct_0 @ X26))),
% 0.36/0.59      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.36/0.59  thf('45', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.59  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('47', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['45', '46'])).
% 0.36/0.59  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('49', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.36/0.59      inference('clc', [status(thm)], ['47', '48'])).
% 0.36/0.59  thf('50', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('51', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['49', '50'])).
% 0.36/0.59  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('53', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['49', '50'])).
% 0.36/0.59  thf('54', plain,
% 0.36/0.59      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['42', '51', '52', '53'])).
% 0.36/0.59  thf('55', plain,
% 0.36/0.59      (![X20 : $i, X21 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X20)
% 0.36/0.59          | ~ (m1_subset_1 @ X21 @ X20)
% 0.36/0.59          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.59  thf('56', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.36/0.59            = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.59  thf('57', plain,
% 0.36/0.59      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['42', '51', '52', '53'])).
% 0.36/0.59  thf(t36_tex_2, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.59           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.36/0.59  thf('58', plain,
% 0.36/0.59      (![X31 : $i, X32 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.36/0.59          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X32) @ X31) @ X32)
% 0.36/0.59          | ~ (l1_pre_topc @ X32)
% 0.36/0.59          | ~ (v2_pre_topc @ X32)
% 0.36/0.59          | (v2_struct_0 @ X32))),
% 0.36/0.59      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.36/0.59  thf('59', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.59           sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.59  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('62', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.59           sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.36/0.59  thf('63', plain,
% 0.36/0.59      (((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.59         sk_A)
% 0.36/0.59        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('simplify', [status(thm)], ['62'])).
% 0.36/0.59  thf('64', plain,
% 0.36/0.59      (((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['56', '63'])).
% 0.36/0.59  thf('65', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.36/0.59      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.59  thf('66', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('67', plain,
% 0.36/0.59      (![X25 : $i, X26 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X25)
% 0.36/0.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.59          | ~ (v2_struct_0 @ (sk_C @ X25 @ X26))
% 0.36/0.59          | ~ (l1_pre_topc @ X26)
% 0.36/0.59          | (v2_struct_0 @ X26))),
% 0.36/0.59      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.36/0.59  thf('68', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['66', '67'])).
% 0.36/0.59  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('70', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['68', '69'])).
% 0.36/0.59  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('72', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['70', '71'])).
% 0.36/0.59  thf('73', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('74', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['72', '73'])).
% 0.36/0.59  thf('75', plain,
% 0.36/0.59      (((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['65', '74'])).
% 0.36/0.59  thf('76', plain,
% 0.36/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.59        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['29', '75'])).
% 0.36/0.59  thf('77', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.36/0.59        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('simplify', [status(thm)], ['76'])).
% 0.36/0.59  thf('78', plain,
% 0.36/0.59      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.59         | (v1_xboole_0 @ sk_B_1)
% 0.36/0.59         | (v2_struct_0 @ sk_A)
% 0.36/0.59         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['10', '77'])).
% 0.36/0.59  thf('79', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(cc1_subset_1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.59  thf('80', plain,
% 0.36/0.59      (![X4 : $i, X5 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.36/0.59          | (v1_xboole_0 @ X4)
% 0.36/0.59          | ~ (v1_xboole_0 @ X5))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.59  thf('81', plain,
% 0.36/0.59      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['79', '80'])).
% 0.36/0.59  thf('82', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('83', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['81', '82'])).
% 0.36/0.59  thf('84', plain,
% 0.36/0.59      ((((v2_struct_0 @ sk_A)
% 0.36/0.59         | (v1_xboole_0 @ sk_B_1)
% 0.36/0.59         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['78', '83'])).
% 0.36/0.59  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('86', plain,
% 0.36/0.59      ((((v2_tex_2 @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.36/0.59         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.59      inference('clc', [status(thm)], ['84', '85'])).
% 0.36/0.59  thf('87', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('88', plain,
% 0.36/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.59      inference('clc', [status(thm)], ['86', '87'])).
% 0.36/0.59  thf('89', plain,
% 0.36/0.59      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('split', [status(esa)], ['8'])).
% 0.36/0.59  thf('90', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['88', '89'])).
% 0.36/0.59  thf('91', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.36/0.59      inference('split', [status(esa)], ['6'])).
% 0.36/0.59  thf('92', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('sat_resolution*', [status(thm)], ['9', '90', '91'])).
% 0.36/0.59  thf('93', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['7', '92'])).
% 0.36/0.59  thf('94', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['5', '93'])).
% 0.36/0.59  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('96', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['94', '95'])).
% 0.36/0.59  thf('97', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('98', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['96', '97'])).
% 0.36/0.59  thf('99', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('100', plain,
% 0.36/0.59      (![X29 : $i, X30 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X29)
% 0.36/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.36/0.59          | ~ (v2_tex_2 @ X29 @ X30)
% 0.36/0.59          | (m1_pre_topc @ (sk_C_1 @ X29 @ X30) @ X30)
% 0.36/0.59          | ~ (l1_pre_topc @ X30)
% 0.36/0.59          | ~ (v2_pre_topc @ X30)
% 0.36/0.59          | (v2_struct_0 @ X30))),
% 0.36/0.59      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.36/0.59  thf('101', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.36/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['99', '100'])).
% 0.36/0.59  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('104', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.36/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.36/0.59  thf('105', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['7', '92'])).
% 0.36/0.59  thf('106', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['104', '105'])).
% 0.36/0.59  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('108', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['106', '107'])).
% 0.36/0.59  thf('109', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('110', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['108', '109'])).
% 0.36/0.59  thf(cc32_tex_2, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.36/0.59         ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.59           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.36/0.59             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.36/0.59  thf('111', plain,
% 0.36/0.59      (![X23 : $i, X24 : $i]:
% 0.36/0.59         (~ (m1_pre_topc @ X23 @ X24)
% 0.36/0.59          | ~ (v1_tdlat_3 @ X23)
% 0.36/0.59          | (v7_struct_0 @ X23)
% 0.36/0.59          | (v2_struct_0 @ X23)
% 0.36/0.59          | ~ (l1_pre_topc @ X24)
% 0.36/0.59          | ~ (v2_tdlat_3 @ X24)
% 0.36/0.59          | ~ (v2_pre_topc @ X24)
% 0.36/0.59          | (v2_struct_0 @ X24))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.36/0.59  thf('112', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (v2_tdlat_3 @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['110', '111'])).
% 0.36/0.59  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('114', plain, ((v2_tdlat_3 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('116', plain,
% 0.36/0.59      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('split', [status(esa)], ['6'])).
% 0.36/0.59  thf('117', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('118', plain,
% 0.36/0.59      (![X29 : $i, X30 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X29)
% 0.36/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.36/0.59          | ~ (v2_tex_2 @ X29 @ X30)
% 0.36/0.59          | (v1_tdlat_3 @ (sk_C_1 @ X29 @ X30))
% 0.36/0.59          | ~ (l1_pre_topc @ X30)
% 0.36/0.59          | ~ (v2_pre_topc @ X30)
% 0.36/0.59          | (v2_struct_0 @ X30))),
% 0.36/0.59      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.36/0.59  thf('119', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['117', '118'])).
% 0.36/0.59  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('122', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.36/0.59  thf('123', plain,
% 0.36/0.59      ((((v1_xboole_0 @ sk_B_1)
% 0.36/0.59         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['116', '122'])).
% 0.36/0.59  thf('124', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('125', plain,
% 0.36/0.59      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.36/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['123', '124'])).
% 0.36/0.59  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('127', plain,
% 0.36/0.59      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.36/0.59         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['125', '126'])).
% 0.36/0.59  thf('128', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('sat_resolution*', [status(thm)], ['9', '90', '91'])).
% 0.36/0.59  thf('129', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['127', '128'])).
% 0.36/0.59  thf('130', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['112', '113', '114', '115', '129'])).
% 0.36/0.59  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('132', plain,
% 0.36/0.59      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['130', '131'])).
% 0.36/0.59  thf('133', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('134', plain,
% 0.36/0.59      (![X29 : $i, X30 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X29)
% 0.36/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.36/0.59          | ~ (v2_tex_2 @ X29 @ X30)
% 0.36/0.59          | ((X29) = (u1_struct_0 @ (sk_C_1 @ X29 @ X30)))
% 0.36/0.59          | ~ (l1_pre_topc @ X30)
% 0.36/0.59          | ~ (v2_pre_topc @ X30)
% 0.36/0.59          | (v2_struct_0 @ X30))),
% 0.36/0.59      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.36/0.59  thf('135', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.36/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['133', '134'])).
% 0.36/0.59  thf('136', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('138', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['7', '92'])).
% 0.36/0.59  thf('139', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.36/0.59        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 0.36/0.59  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('141', plain,
% 0.36/0.59      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.59        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.36/0.59      inference('clc', [status(thm)], ['139', '140'])).
% 0.36/0.59  thf('142', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('143', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['141', '142'])).
% 0.36/0.59  thf(fc7_struct_0, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.59       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.36/0.59  thf('144', plain,
% 0.36/0.59      (![X14 : $i]:
% 0.36/0.59         ((v1_zfmisc_1 @ (u1_struct_0 @ X14))
% 0.36/0.59          | ~ (l1_struct_0 @ X14)
% 0.36/0.59          | ~ (v7_struct_0 @ X14))),
% 0.36/0.59      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.36/0.59  thf('145', plain,
% 0.36/0.59      (((v1_zfmisc_1 @ sk_B_1)
% 0.36/0.59        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['143', '144'])).
% 0.36/0.59  thf('146', plain,
% 0.36/0.59      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.59      inference('split', [status(esa)], ['8'])).
% 0.36/0.59  thf('147', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.36/0.59      inference('sat_resolution*', [status(thm)], ['9', '90'])).
% 0.36/0.59  thf('148', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['146', '147'])).
% 0.36/0.59  thf('149', plain,
% 0.36/0.59      ((~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['145', '148'])).
% 0.36/0.59  thf('150', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['108', '109'])).
% 0.36/0.59  thf(dt_m1_pre_topc, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( l1_pre_topc @ A ) =>
% 0.36/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.36/0.59  thf('151', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i]:
% 0.36/0.59         (~ (m1_pre_topc @ X12 @ X13)
% 0.36/0.59          | (l1_pre_topc @ X12)
% 0.36/0.59          | ~ (l1_pre_topc @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.59  thf('152', plain,
% 0.36/0.59      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['150', '151'])).
% 0.36/0.59  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('154', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['152', '153'])).
% 0.36/0.59  thf(dt_l1_pre_topc, axiom,
% 0.36/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.59  thf('155', plain,
% 0.36/0.59      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.59  thf('156', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['154', '155'])).
% 0.36/0.59  thf('157', plain, (~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['149', '156'])).
% 0.36/0.59  thf('158', plain, ((v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['132', '157'])).
% 0.36/0.59  thf('159', plain, ($false), inference('demod', [status(thm)], ['98', '158'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
