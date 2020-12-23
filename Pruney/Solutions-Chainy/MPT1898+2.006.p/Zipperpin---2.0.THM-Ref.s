%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tOkmkL2sSc

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 306 expanded)
%              Number of leaves         :   28 ( 104 expanded)
%              Depth                    :   22
%              Number of atoms          :  951 (3390 expanded)
%              Number of equality atoms :   36 (  84 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d6_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( v3_tex_2 @ ( sk_C_1 @ X20 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v3_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('15',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ( m1_subset_1 @ ( sk_C_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v3_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t66_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_tex_2 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ? [B: $i] :
            ( ( v3_tex_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tex_2])).

thf('20',plain,(
    ! [X22: $i] :
      ( ~ ( v3_tex_2 @ X22 @ sk_A )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A )
    | ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['33','34'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X15: $i] :
      ( ( v4_pre_topc @ ( sk_B @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('37',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( sk_B @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('41',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('42',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X19 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X19 )
       != ( sk_C @ X16 @ X17 ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( sk_B @ X0 ) )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( sk_B @ X0 ) )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( sk_B @ X0 ) )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('64',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X22: $i] :
      ( ~ ( v3_tex_2 @ X22 @ sk_A )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ~ ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['60','61'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('75',plain,
    ( ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['72','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tOkmkL2sSc
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:29:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 116 iterations in 0.066s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(t4_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.52  thf(d6_tex_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.52             ( ![C:$i]:
% 0.21/0.52               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.21/0.52                      ( ![D:$i]:
% 0.21/0.52                        ( ( m1_subset_1 @
% 0.21/0.52                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.52                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.52                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.52          | (r1_tarski @ (sk_C @ X16 @ X17) @ X16)
% 0.21/0.52          | (v2_tex_2 @ X16 @ X17)
% 0.21/0.52          | ~ (l1_pre_topc @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X0)
% 0.21/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.52          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.52  thf(t3_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('5', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.52  thf(t65_tex_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.21/0.52                ( ![C:$i]:
% 0.21/0.52                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.52          | ~ (v2_tex_2 @ X20 @ X21)
% 0.21/0.52          | (v3_tex_2 @ (sk_C_1 @ X20 @ X21) @ X21)
% 0.21/0.52          | ~ (l1_pre_topc @ X21)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X21)
% 0.21/0.52          | ~ (v2_pre_topc @ X21)
% 0.21/0.52          | (v2_struct_0 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.52          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.52          | (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.52          | ~ (v2_tex_2 @ X20 @ X21)
% 0.21/0.52          | (m1_subset_1 @ (sk_C_1 @ X20 @ X21) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.52          | ~ (l1_pre_topc @ X21)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X21)
% 0.21/0.52          | ~ (v2_pre_topc @ X21)
% 0.21/0.52          | (v2_struct_0 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.52          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.52          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.52  thf(t66_tex_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ?[B:$i]:
% 0.21/0.52         ( ( v3_tex_2 @ B @ A ) & 
% 0.21/0.52           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ?[B:$i]:
% 0.21/0.52            ( ( v3_tex_2 @ B @ A ) & 
% 0.21/0.52              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         (~ (v3_tex_2 @ X22 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.21/0.52  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      ((~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)
% 0.21/0.52        | ((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '27'])).
% 0.21/0.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A) | ((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.52  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf(rc7_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ?[B:$i]:
% 0.21/0.52         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.52           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X15 : $i]:
% 0.21/0.52         ((v4_pre_topc @ (sk_B @ X15) @ X15)
% 0.21/0.52          | ~ (l1_pre_topc @ X15)
% 0.21/0.52          | ~ (v2_pre_topc @ X15)
% 0.21/0.52          | (v2_struct_0 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X15 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (sk_B @ X15) @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.52          | ~ (l1_pre_topc @ X15)
% 0.21/0.52          | ~ (v2_pre_topc @ X15)
% 0.21/0.52          | (v2_struct_0 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.52  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.52         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.21/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (sk_B @ X0))
% 0.21/0.52              = (k3_xboole_0 @ X1 @ (sk_B @ X0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X15 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (sk_B @ X15) @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.52          | ~ (l1_pre_topc @ X15)
% 0.21/0.52          | ~ (v2_pre_topc @ X15)
% 0.21/0.52          | (v2_struct_0 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.52          | ~ (v4_pre_topc @ X19 @ X17)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X19)
% 0.21/0.52              != (sk_C @ X16 @ X17))
% 0.21/0.52          | (v2_tex_2 @ X16 @ X17)
% 0.21/0.52          | ~ (l1_pre_topc @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X0)
% 0.21/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.21/0.52              != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.52          | ~ (v4_pre_topc @ X1 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ (sk_B @ X0))
% 0.21/0.52              != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ (sk_B @ X0))
% 0.21/0.52              != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.52          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ k1_xboole_0 @ (sk_B @ X0))
% 0.21/0.52            != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 0.21/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '45'])).
% 0.21/0.52  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf(t17_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.21/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.21/0.52          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 0.21/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['46', '51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.52          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '53'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.52          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '55'])).
% 0.21/0.52  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.52  thf('60', plain, (((v2_tex_2 @ k1_xboole_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.52  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.52          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (((m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('66', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (((m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.21/0.52  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      ((m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         (~ (v3_tex_2 @ X22 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('72', plain, (~ (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (v2_pre_topc @ X0)
% 0.21/0.52          | ~ (v3_tdlat_3 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.52          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (((v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v3_tdlat_3 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.52  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('77', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (((v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.21/0.52  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('81', plain, ((v3_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['79', '80'])).
% 0.21/0.52  thf('82', plain, ($false), inference('demod', [status(thm)], ['72', '81'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
