%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UrqnPwKs9b

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 127 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   21
%              Number of atoms          :  732 (1611 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc11_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v2_tdlat_3 @ B )
          & ( v1_tdlat_3 @ B )
          & ( v2_pre_topc @ B )
          & ( v1_pre_topc @ B )
          & ~ ( v2_struct_0 @ B )
          & ( m1_pre_topc @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X2 ) @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc11_tex_2])).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_tdlat_3 @ ( sk_B @ X2 ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc11_tex_2])).

thf('3',plain,(
    ! [X2: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X2 ) @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc11_tex_2])).

thf(l17_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( X5
       != ( u1_struct_0 @ X3 ) )
      | ~ ( v1_tdlat_3 @ X3 )
      | ( v2_tex_2 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X3 ) @ X4 )
      | ~ ( v1_tdlat_3 @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_tex_2 @ X6 @ X7 )
      | ( v3_tex_2 @ ( sk_C @ X6 @ X7 ) @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v3_tdlat_3 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_tex_2 @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_C @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v3_tdlat_3 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X8: $i] :
      ( ~ ( v3_tex_2 @ X8 @ sk_A )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_struct_0 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X2 ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc11_tex_2])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UrqnPwKs9b
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:41:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 29 iterations in 0.022s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.47  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.47  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.47  thf(t66_tex_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.47         ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ?[B:$i]:
% 0.20/0.47         ( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.47           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ?[B:$i]:
% 0.20/0.47            ( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.47              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.20/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(rc11_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ?[B:$i]:
% 0.20/0.47         ( ( v2_tdlat_3 @ B ) & ( v1_tdlat_3 @ B ) & ( v2_pre_topc @ B ) & 
% 0.20/0.47           ( v1_pre_topc @ B ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.20/0.47           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X2 : $i]:
% 0.20/0.47         ((m1_pre_topc @ (sk_B @ X2) @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X2)
% 0.20/0.47          | (v2_struct_0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [rc11_tex_2])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X2 : $i]:
% 0.20/0.47         ((v1_tdlat_3 @ (sk_B @ X2))
% 0.20/0.47          | ~ (l1_pre_topc @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X2)
% 0.20/0.47          | (v2_struct_0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [rc11_tex_2])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X2 : $i]:
% 0.20/0.47         ((m1_pre_topc @ (sk_B @ X2) @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X2)
% 0.20/0.47          | (v2_struct_0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [rc11_tex_2])).
% 0.20/0.47  thf(l17_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.47           ( m1_subset_1 @
% 0.20/0.47             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.47          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.47          | ~ (l1_pre_topc @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [l17_tex_2])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.47  thf(t26_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.47                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X3)
% 0.20/0.47          | ~ (m1_pre_topc @ X3 @ X4)
% 0.20/0.47          | ((X5) != (u1_struct_0 @ X3))
% 0.20/0.47          | ~ (v1_tdlat_3 @ X3)
% 0.20/0.47          | (v2_tex_2 @ X5 @ X4)
% 0.20/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.47          | ~ (l1_pre_topc @ X4)
% 0.20/0.47          | (v2_struct_0 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X4)
% 0.20/0.47          | ~ (l1_pre_topc @ X4)
% 0.20/0.47          | ~ (m1_subset_1 @ (u1_struct_0 @ X3) @ 
% 0.20/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.47          | (v2_tex_2 @ (u1_struct_0 @ X3) @ X4)
% 0.20/0.47          | ~ (v1_tdlat_3 @ X3)
% 0.20/0.47          | ~ (m1_pre_topc @ X3 @ X4)
% 0.20/0.47          | (v2_struct_0 @ X3))),
% 0.20/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.20/0.47          | ~ (v1_tdlat_3 @ (sk_B @ X0))
% 0.20/0.47          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.47          | ~ (v1_tdlat_3 @ (sk_B @ X0))
% 0.20/0.47          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.20/0.47          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.47          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.47  thf(t65_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.47         ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.47                ( ![C:$i]:
% 0.20/0.47                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.47          | ~ (v2_tex_2 @ X6 @ X7)
% 0.20/0.47          | (v3_tex_2 @ (sk_C @ X6 @ X7) @ X7)
% 0.20/0.47          | ~ (l1_pre_topc @ X7)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X7)
% 0.20/0.47          | ~ (v2_pre_topc @ X7)
% 0.20/0.47          | (v2_struct_0 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v3_tex_2 @ (sk_C @ (u1_struct_0 @ (sk_B @ X0)) @ X0) @ X0)
% 0.20/0.47          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.47          | (v3_tex_2 @ (sk_C @ (u1_struct_0 @ (sk_B @ X0)) @ X0) @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | (v3_tex_2 @ (sk_C @ (u1_struct_0 @ (sk_B @ X0)) @ X0) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v3_tex_2 @ (sk_C @ (u1_struct_0 @ (sk_B @ X0)) @ X0) @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.47          | ~ (v2_tex_2 @ X6 @ X7)
% 0.20/0.47          | (m1_subset_1 @ (sk_C @ X6 @ X7) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.47          | ~ (l1_pre_topc @ X7)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X7)
% 0.20/0.47          | ~ (v2_pre_topc @ X7)
% 0.20/0.47          | (v2_struct_0 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ (sk_B @ X0)) @ X0) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.20/0.47          | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ (sk_B @ X0)) @ X0) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ (sk_B @ X0)) @ X0) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (sk_C @ (u1_struct_0 @ (sk_B @ X0)) @ X0) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.47          | (v2_struct_0 @ (sk_B @ X0))
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v2_struct_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X8 : $i]:
% 0.20/0.47         (~ (v3_tex_2 @ X8 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ (sk_B @ sk_A))
% 0.20/0.47        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.47        | ~ (v3_tex_2 @ (sk_C @ (u1_struct_0 @ (sk_B @ sk_A)) @ sk_A) @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ (sk_B @ sk_A))
% 0.20/0.47        | ~ (v3_tex_2 @ (sk_C @ (u1_struct_0 @ (sk_B @ sk_A)) @ sk_A) @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.20/0.47  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((~ (v3_tex_2 @ (sk_C @ (u1_struct_0 @ (sk_B @ sk_A)) @ sk_A) @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ (sk_B @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ (sk_B @ sk_A))
% 0.20/0.47        | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ (sk_B @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '35'])).
% 0.20/0.47  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('39', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ (sk_B @ sk_A))
% 0.20/0.47        | (v2_struct_0 @ (sk_B @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.20/0.47  thf('41', plain, (((v2_struct_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.47  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('43', plain, ((v2_struct_0 @ (sk_B @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X2 : $i]:
% 0.20/0.47         (~ (v2_struct_0 @ (sk_B @ X2))
% 0.20/0.47          | ~ (l1_pre_topc @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X2)
% 0.20/0.47          | (v2_struct_0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [rc11_tex_2])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.47  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('48', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.20/0.47  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
