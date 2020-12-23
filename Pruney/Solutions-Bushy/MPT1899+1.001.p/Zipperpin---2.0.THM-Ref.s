%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1899+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5hLXLxhhHc

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  157 (2701 expanded)
%              Number of leaves         :   26 ( 786 expanded)
%              Depth                    :   23
%              Number of atoms          : 1429 (46370 expanded)
%              Number of equality atoms :   11 ( 110 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t67_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v1_tdlat_3 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ? [C: $i] :
              ( ( v4_tex_2 @ C @ A )
              & ( m1_pre_topc @ B @ C )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ? [C: $i] :
                ( ( v4_tex_2 @ C @ A )
                & ( m1_pre_topc @ B @ C )
                & ( m1_pre_topc @ C @ A )
                & ( v1_pre_topc @ C )
                & ~ ( v2_struct_0 @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_C_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( X4
       != ( u1_struct_0 @ X2 ) )
      | ~ ( v1_tdlat_3 @ X2 )
      | ( v2_tex_2 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X2 ) @ X3 )
      | ~ ( v1_tdlat_3 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t53_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v3_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ~ ( ( v4_tex_2 @ C @ A )
                      & ( B
                        = ( u1_struct_0 @ C ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_tex_2 @ X10 @ X11 )
      | ( v4_tex_2 @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t53_tex_2])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( v3_tex_2 @ ( sk_C_1 @ X12 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( v4_tex_2 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    v4_tex_2 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X14: $i] :
      ( ~ ( v4_tex_2 @ X14 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X14 )
      | ~ ( m1_pre_topc @ X14 @ sk_A )
      | ~ ( v1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_tex_2 @ X10 @ X11 )
      | ( m1_pre_topc @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t53_tex_2])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('64',plain,(
    m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','64'])).

thf('66',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_tex_2 @ X10 @ X11 )
      | ~ ( v2_struct_0 @ ( sk_C @ X10 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t53_tex_2])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ~ ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['65','76'])).

thf('78',plain,(
    m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_tex_2 @ X10 @ X11 )
      | ( v1_pre_topc @ ( sk_C @ X10 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t53_tex_2])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ sk_A ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ sk_A ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    m1_subset_1 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('89',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_tex_2 @ X10 @ X11 )
      | ( X10
        = ( u1_struct_0 @ ( sk_C @ X10 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t53_tex_2])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) )
    | ~ ( v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('98',plain,
    ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('100',plain,(
    v3_tex_2 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('101',plain,
    ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','98','99','100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ( v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('106',plain,(
    v1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','106'])).

thf('108',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('109',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( sk_C_1 @ X12 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('119',plain,
    ( ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    = ( u1_struct_0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('120',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X9 ) )
      | ( m1_pre_topc @ X7 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) @ X1 )
      | ( m1_pre_topc @ X0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ X0 @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_pre_topc @ sk_B @ ( sk_C @ ( sk_C_1 @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['107','128'])).


%------------------------------------------------------------------------------
