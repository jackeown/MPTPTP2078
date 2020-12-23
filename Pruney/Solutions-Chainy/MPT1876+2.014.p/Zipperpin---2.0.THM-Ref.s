%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nGEz8w9SEu

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  203 (2663 expanded)
%              Number of leaves         :   36 ( 714 expanded)
%              Depth                    :   36
%              Number of atoms          : 1547 (35909 expanded)
%              Number of equality atoms :   25 ( 491 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X20 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( X16
        = ( k6_domain_1 @ X16 @ ( sk_B @ X16 ) ) )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('11',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( m1_subset_1 @ ( sk_B @ X16 ) @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( ( k6_domain_1 @ X9 @ X10 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X18 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X18
        = ( u1_struct_0 @ ( sk_C @ X18 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( m1_subset_1 @ ( sk_B @ X16 ) @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

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

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('41',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
      | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_B_1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 )
        | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','42'])).

thf('44',plain,
    ( ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( ( k6_domain_1 @ X9 @ X10 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('48',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('51',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_zfmisc_1 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['16','57'])).

thf('59',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('60',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X18 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('83',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('85',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','83','84'])).

thf('86',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( m1_pre_topc @ ( sk_C_1 @ X20 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','85'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['101','102'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('104',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

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

thf('108',plain,(
    ! [X13: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( v1_tdlat_3 @ X13 )
      | ~ ( v2_tdlat_3 @ X13 )
      | ( v7_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('109',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X20 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','83','84'])).

thf('123',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','123'])).

thf('125',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['101','102'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('126',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_tdlat_3 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('135',plain,(
    ! [X11: $i] :
      ( ~ ( v1_tdlat_3 @ X11 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('136',plain,
    ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['121','122'])).

thf('138',plain,(
    v2_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','133','138'])).

thf('140',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('141',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( X20
        = ( u1_struct_0 @ ( sk_C_1 @ X20 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','146'])).

thf('148',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['149','150'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('152',plain,(
    ! [X5: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ~ ( v7_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('153',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','83','84'])).

thf('155',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('157',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','83'])).

thf('158',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['155','158'])).

thf('160',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('161',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('162',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['159','162'])).

thf('164',plain,(
    v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['139','163'])).

thf('165',plain,(
    $false ),
    inference(demod,[status(thm)],['91','164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nGEz8w9SEu
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 137 iterations in 0.093s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(t44_tex_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t34_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.52                ( ![C:$i]:
% 0.20/0.52                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.52                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X20)
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.52          | ~ (v2_tex_2 @ X20 @ X21)
% 0.20/0.52          | ~ (v2_struct_0 @ (sk_C_1 @ X20 @ X21))
% 0.20/0.52          | ~ (l1_pre_topc @ X21)
% 0.20/0.52          | ~ (v2_pre_topc @ X21)
% 0.20/0.52          | (v2_struct_0 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.52  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf(d1_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52       ( ( v1_zfmisc_1 @ A ) <=>
% 0.20/0.52         ( ?[B:$i]:
% 0.20/0.52           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X16 : $i]:
% 0.20/0.52         (~ (v1_zfmisc_1 @ X16)
% 0.20/0.52          | ((X16) = (k6_domain_1 @ X16 @ (sk_B @ X16)))
% 0.20/0.52          | (v1_xboole_0 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X16 : $i]:
% 0.20/0.52         (~ (v1_zfmisc_1 @ X16)
% 0.20/0.52          | (m1_subset_1 @ (sk_B @ X16) @ X16)
% 0.20/0.52          | (v1_xboole_0 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X9)
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ X9)
% 0.20/0.52          | ((k6_domain_1 @ X9 @ X10) = (k1_tarski @ X10)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.52          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.52          | (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.52          | (v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['10', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ X0)
% 0.20/0.52          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t10_tsep_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52           ( ?[C:$i]:
% 0.20/0.52             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.20/0.52               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X18)
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.52          | (m1_pre_topc @ (sk_C @ X18 @ X19) @ X19)
% 0.20/0.52          | ~ (l1_pre_topc @ X19)
% 0.20/0.52          | (v2_struct_0 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X18)
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.52          | ((X18) = (u1_struct_0 @ (sk_C @ X18 @ X19)))
% 0.20/0.52          | ~ (l1_pre_topc @ X19)
% 0.20/0.52          | (v2_struct_0 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.52        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.20/0.52      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X16 : $i]:
% 0.20/0.52         (~ (v1_zfmisc_1 @ X16)
% 0.20/0.52          | (m1_subset_1 @ (sk_B @ X16) @ X16)
% 0.20/0.52          | (v1_xboole_0 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.52  thf(t55_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.52               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X6)
% 0.20/0.52          | ~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.52          | (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.52          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 0.20/0.52          | ~ (l1_pre_topc @ X7)
% 0.20/0.52          | (v2_struct_0 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | ~ (l1_pre_topc @ X1)
% 0.20/0.52          | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ X0)) @ (u1_struct_0 @ X1))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.52          | (v2_struct_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52          | ~ (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.52          | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.20/0.52             (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '38'])).
% 0.20/0.52  thf('40', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('41', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.52          | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52          | ~ (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.52          | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((v1_xboole_0 @ sk_B_1)
% 0.20/0.52           | (v2_struct_0 @ X0)
% 0.20/0.52           | ~ (l1_pre_topc @ X0)
% 0.20/0.52           | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ X0))
% 0.20/0.52           | ~ (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ X0)
% 0.20/0.52           | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.52         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      ((((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '43'])).
% 0.20/0.52  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X9)
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ X9)
% 0.20/0.52          | ((k6_domain_1 @ X9 @ X10) = (k1_tarski @ X10)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.20/0.52             = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      ((((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf(t36_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.20/0.52          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.20/0.52          | ~ (l1_pre_topc @ X23)
% 0.20/0.52          | ~ (v2_pre_topc @ X23)
% 0.20/0.52          | (v2_struct_0 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52         | (v2_tex_2 @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_A)))
% 0.20/0.52         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_tex_2 @ 
% 0.20/0.52            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_A)))
% 0.20/0.52         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.52          sk_A)
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      ((((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 0.20/0.52         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['48', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)))
% 0.20/0.52         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['16', '57'])).
% 0.20/0.52  thf('59', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X18)
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.52          | ~ (v2_struct_0 @ (sk_C @ X18 @ X19))
% 0.20/0.52          | ~ (l1_pre_topc @ X19)
% 0.20/0.52          | (v2_struct_0 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.52  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.52  thf('69', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('70', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['61', '70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc1_subset_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.52          | (v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.52  thf('75', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('76', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | (v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['71', '76'])).
% 0.20/0.52  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      ((((v2_tex_2 @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.20/0.52         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('clc', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('80', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('clc', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('82', plain,
% 0.20/0.52      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('83', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.52  thf('84', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('85', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['9', '83', '84'])).
% 0.20/0.52  thf('86', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['7', '85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '86'])).
% 0.20/0.52  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['87', '88'])).
% 0.20/0.52  thf('90', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('91', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('93', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X20)
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.52          | ~ (v2_tex_2 @ X20 @ X21)
% 0.20/0.52          | (m1_pre_topc @ (sk_C_1 @ X20 @ X21) @ X21)
% 0.20/0.52          | ~ (l1_pre_topc @ X21)
% 0.20/0.52          | ~ (v2_pre_topc @ X21)
% 0.20/0.52          | (v2_struct_0 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.52  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('97', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.20/0.52  thf('98', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['7', '85'])).
% 0.20/0.52  thf('99', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['97', '98'])).
% 0.20/0.52  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('101', plain,
% 0.20/0.52      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.52        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['99', '100'])).
% 0.20/0.52  thf('102', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('103', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.52      inference('clc', [status(thm)], ['101', '102'])).
% 0.20/0.52  thf(dt_m1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.52  thf('104', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.52  thf('105', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.52  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('107', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['105', '106'])).
% 0.20/0.52  thf(cc2_tex_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.20/0.52         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.20/0.52  thf('108', plain,
% 0.20/0.52      (![X13 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X13)
% 0.20/0.52          | ~ (v2_pre_topc @ X13)
% 0.20/0.52          | ~ (v1_tdlat_3 @ X13)
% 0.20/0.52          | ~ (v2_tdlat_3 @ X13)
% 0.20/0.52          | (v7_struct_0 @ X13)
% 0.20/0.52          | ~ (l1_pre_topc @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.20/0.52  thf('109', plain,
% 0.20/0.52      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['107', '108'])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('111', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('112', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X20)
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.52          | ~ (v2_tex_2 @ X20 @ X21)
% 0.20/0.52          | (v1_tdlat_3 @ (sk_C_1 @ X20 @ X21))
% 0.20/0.52          | ~ (l1_pre_topc @ X21)
% 0.20/0.52          | ~ (v2_pre_topc @ X21)
% 0.20/0.52          | (v2_struct_0 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.52  thf('113', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.52  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('116', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.20/0.52  thf('117', plain,
% 0.20/0.52      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['110', '116'])).
% 0.20/0.52  thf('118', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('119', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.20/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['117', '118'])).
% 0.20/0.52  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('121', plain,
% 0.20/0.52      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['119', '120'])).
% 0.20/0.52  thf('122', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['9', '83', '84'])).
% 0.20/0.52  thf('123', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['121', '122'])).
% 0.20/0.52  thf('124', plain,
% 0.20/0.52      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['109', '123'])).
% 0.20/0.52  thf('125', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.20/0.52      inference('clc', [status(thm)], ['101', '102'])).
% 0.20/0.52  thf(cc6_tdlat_3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.20/0.52  thf('126', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.52          | (v2_tdlat_3 @ X14)
% 0.20/0.52          | ~ (l1_pre_topc @ X15)
% 0.20/0.52          | ~ (v2_tdlat_3 @ X15)
% 0.20/0.52          | ~ (v2_pre_topc @ X15)
% 0.20/0.52          | (v2_struct_0 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.20/0.52  thf('127', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['125', '126'])).
% 0.20/0.52  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('129', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('131', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 0.20/0.52  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('133', plain, ((v2_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['131', '132'])).
% 0.20/0.52  thf('134', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['105', '106'])).
% 0.20/0.52  thf(cc1_tdlat_3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) => ( ( v1_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.20/0.52  thf('135', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v1_tdlat_3 @ X11) | (v2_pre_topc @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_tdlat_3])).
% 0.20/0.52  thf('136', plain,
% 0.20/0.52      (((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['134', '135'])).
% 0.20/0.52  thf('137', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['121', '122'])).
% 0.20/0.52  thf('138', plain, ((v2_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['136', '137'])).
% 0.20/0.52  thf('139', plain,
% 0.20/0.52      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['124', '133', '138'])).
% 0.20/0.52  thf('140', plain,
% 0.20/0.52      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('141', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('142', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X20)
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.52          | ~ (v2_tex_2 @ X20 @ X21)
% 0.20/0.52          | ((X20) = (u1_struct_0 @ (sk_C_1 @ X20 @ X21)))
% 0.20/0.52          | ~ (l1_pre_topc @ X21)
% 0.20/0.52          | ~ (v2_pre_topc @ X21)
% 0.20/0.52          | (v2_struct_0 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.52  thf('143', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['141', '142'])).
% 0.20/0.52  thf('144', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('146', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.20/0.52  thf('147', plain,
% 0.20/0.52      ((((v1_xboole_0 @ sk_B_1)
% 0.20/0.52         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.20/0.52         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['140', '146'])).
% 0.20/0.52  thf('148', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('149', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A)
% 0.20/0.52         | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))))
% 0.20/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['147', '148'])).
% 0.20/0.52  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('151', plain,
% 0.20/0.52      ((((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.20/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['149', '150'])).
% 0.20/0.52  thf(fc7_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.52  thf('152', plain,
% 0.20/0.52      (![X5 : $i]:
% 0.20/0.52         ((v1_zfmisc_1 @ (u1_struct_0 @ X5))
% 0.20/0.52          | ~ (l1_struct_0 @ X5)
% 0.20/0.52          | ~ (v7_struct_0 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.20/0.52  thf('153', plain,
% 0.20/0.52      ((((v1_zfmisc_1 @ sk_B_1)
% 0.20/0.52         | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52         | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.20/0.52         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['151', '152'])).
% 0.20/0.52  thf('154', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['9', '83', '84'])).
% 0.20/0.52  thf('155', plain,
% 0.20/0.52      (((v1_zfmisc_1 @ sk_B_1)
% 0.20/0.52        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['153', '154'])).
% 0.20/0.52  thf('156', plain,
% 0.20/0.52      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('157', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['9', '83'])).
% 0.20/0.52  thf('158', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['156', '157'])).
% 0.20/0.52  thf('159', plain,
% 0.20/0.52      ((~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.20/0.52        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['155', '158'])).
% 0.20/0.52  thf('160', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['105', '106'])).
% 0.20/0.52  thf(dt_l1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.52  thf('161', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.52  thf('162', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['160', '161'])).
% 0.20/0.52  thf('163', plain, (~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['159', '162'])).
% 0.20/0.52  thf('164', plain, ((v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['139', '163'])).
% 0.20/0.52  thf('165', plain, ($false), inference('demod', [status(thm)], ['91', '164'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
