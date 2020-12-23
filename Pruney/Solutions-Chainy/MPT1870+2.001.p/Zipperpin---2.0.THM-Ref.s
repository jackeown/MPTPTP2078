%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zuiqqaoilt

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:41 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 321 expanded)
%              Number of leaves         :   19 ( 102 expanded)
%              Depth                    :   19
%              Number of atoms          : 1265 (7607 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t38_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( v3_pre_topc @ C @ A )
                  & ( v2_tex_2 @ B @ A )
                  & ( v2_tex_2 @ C @ A ) )
               => ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_pre_topc @ B @ A )
                    & ( v3_pre_topc @ C @ A )
                    & ( v2_tex_2 @ B @ A )
                    & ( v2_tex_2 @ C @ A ) )
                 => ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_pre_topc @ B @ A )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A )
                    & ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_pre_topc @ B @ A )
                    & ( v3_pre_topc @ C @ A )
                    & ( v2_tex_2 @ B @ A )
                    & ( v2_tex_2 @ C @ A ) )
                 => ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X6 )
      | ~ ( v2_tex_2 @ X7 @ X6 )
      | ~ ( v3_pre_topc @ X8 @ X6 )
      | ~ ( v2_tex_2 @ X8 @ X6 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X6 ) @ X7 @ X8 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_tex_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X6 )
      | ~ ( v2_tex_2 @ X7 @ X6 )
      | ~ ( v3_pre_topc @ X8 @ X6 )
      | ~ ( v2_tex_2 @ X8 @ X6 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X6 ) @ X7 @ X8 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(t37_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( v3_pre_topc @ C @ A ) )
               => ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ~ ( v3_pre_topc @ X2 @ X1 )
      | ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 @ X2 ) @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_tops_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v3_pre_topc @ ( sk_B @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X6 )
      | ~ ( v2_tex_2 @ X7 @ X6 )
      | ~ ( v3_pre_topc @ X8 @ X6 )
      | ~ ( v2_tex_2 @ X8 @ X6 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X6 ) @ X7 @ X8 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
      | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','48'])).

thf('50',plain,
    ( ~ ( v3_pre_topc @ ( sk_C @ sk_A ) @ sk_A )
    | ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v3_pre_topc @ ( sk_C @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X6 )
      | ~ ( v2_tex_2 @ X7 @ X6 )
      | ~ ( v3_pre_topc @ X8 @ X6 )
      | ~ ( v2_tex_2 @ X8 @ X6 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X6 ) @ X7 @ X8 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_tex_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
      | ( v3_pre_topc @ ( sk_C @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( v3_pre_topc @ ( sk_C @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ( v3_pre_topc @ ( sk_C @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v3_pre_topc @ ( sk_C @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_pre_topc @ ( sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['50','64'])).

thf('66',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v3_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ X6 ) @ ( sk_B @ X6 ) @ ( sk_C @ X6 ) ) @ X6 )
      | ~ ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X6 ) @ ( sk_B @ X6 ) @ ( sk_C @ X6 ) ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X6 )
      | ~ ( v2_tex_2 @ X7 @ X6 )
      | ~ ( v3_pre_topc @ X8 @ X6 )
      | ~ ( v2_tex_2 @ X8 @ X6 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X6 ) @ X7 @ X8 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t30_tex_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X1 @ sk_A )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X1 @ sk_A )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('71',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(t38_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( v3_pre_topc @ C @ A ) )
               => ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('72',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_pre_topc @ X3 @ X4 )
      | ~ ( v3_pre_topc @ X5 @ X4 )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X4 ) @ X3 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t38_tops_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['46','47'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,
    ( ~ ( v3_pre_topc @ ( sk_C @ sk_A ) @ sk_A )
    | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    v3_pre_topc @ ( sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('80',plain,(
    v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X1 @ sk_A )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['69','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','81'])).

thf('83',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','85'])).

thf('87',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['0','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zuiqqaoilt
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:51:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 82 iterations in 0.056s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.56  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(t38_tex_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56               ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) & 
% 0.37/0.56                   ( v2_tex_2 @ B @ A ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.37/0.56                 ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                  ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) & 
% 0.37/0.56                      ( v2_tex_2 @ B @ A ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.37/0.56                    ( v2_tex_2 @
% 0.37/0.56                      ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t38_tex_2])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (~ (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56          sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t30_tex_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ( ![B:$i]:
% 0.37/0.56           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56             ( ![C:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                 ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.37/0.56                   ( ( v3_pre_topc @
% 0.37/0.56                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) & 
% 0.37/0.56                     ( v3_pre_topc @
% 0.37/0.56                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) =>
% 0.37/0.56         ( ![B:$i]:
% 0.37/0.56           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56             ( ![C:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                 ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) & 
% 0.37/0.56                     ( v2_tex_2 @ B @ A ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.37/0.56                   ( v2_tex_2 @
% 0.37/0.56                     ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (sk_C @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (v3_pre_topc @ X7 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X7 @ X6)
% 0.37/0.56          | ~ (v3_pre_topc @ X8 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X8 @ X6)
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X6) @ X7 @ X8) @ X6)
% 0.37/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (l1_pre_topc @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t30_tex_2])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.37/0.56             sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.56          | (m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.56  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('8', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('9', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.37/0.56             sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | (m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (((m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56        | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.37/0.56        | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.37/0.56        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '10'])).
% 0.37/0.56  thf('12', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('13', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (((m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (~ (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56          sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('clc', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (v3_pre_topc @ X7 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X7 @ X6)
% 0.37/0.56          | ~ (v3_pre_topc @ X8 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X8 @ X6)
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X6) @ X7 @ X8) @ X6)
% 0.37/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (l1_pre_topc @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t30_tex_2])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.37/0.56             sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.56          | (m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('22', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('23', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.37/0.56             sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | (m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56        | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.37/0.56        | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.37/0.56        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '24'])).
% 0.37/0.56  thf('26', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('27', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (~ (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56          sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('clc', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf(t37_tops_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56               ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.37/0.56                 ( v3_pre_topc @
% 0.37/0.56                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ X1)
% 0.37/0.56          | ~ (v3_pre_topc @ X2 @ X1)
% 0.37/0.56          | (v3_pre_topc @ (k4_subset_1 @ (u1_struct_0 @ X1) @ X0 @ X2) @ X1)
% 0.37/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.37/0.56          | ~ (l1_pre_topc @ X1)
% 0.37/0.56          | ~ (v2_pre_topc @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [t37_tops_1])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v3_pre_topc @ 
% 0.37/0.56             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ X0) @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.56  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         ((v3_pre_topc @ (sk_B @ X6) @ X6)
% 0.37/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (v3_pre_topc @ X7 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X7 @ X6)
% 0.37/0.56          | ~ (v3_pre_topc @ X8 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X8 @ X6)
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X6) @ X7 @ X8) @ X6)
% 0.37/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (l1_pre_topc @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t30_tex_2])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.37/0.56             sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.56          | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.56  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('40', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('41', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.37/0.56             sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | (v3_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (((v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.37/0.56        | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.37/0.56        | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.37/0.56        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['35', '42'])).
% 0.37/0.56  thf('44', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('45', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (((v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.37/0.56        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (~ (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56          sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('48', plain, ((v3_pre_topc @ (sk_B @ sk_A) @ sk_A)),
% 0.37/0.56      inference('clc', [status(thm)], ['46', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v3_pre_topc @ 
% 0.37/0.56             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ X0) @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33', '34', '48'])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      ((~ (v3_pre_topc @ (sk_C @ sk_A) @ sk_A)
% 0.37/0.56        | (v3_pre_topc @ 
% 0.37/0.56           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ (sk_C @ sk_A)) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['16', '49'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         ((v3_pre_topc @ (sk_C @ X6) @ X6)
% 0.37/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (v3_pre_topc @ X7 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X7 @ X6)
% 0.37/0.56          | ~ (v3_pre_topc @ X8 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X8 @ X6)
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X6) @ X7 @ X8) @ X6)
% 0.37/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (l1_pre_topc @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t30_tex_2])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.37/0.56             sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.37/0.56          | (v3_pre_topc @ (sk_C @ sk_A) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.56  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('56', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('57', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.37/0.56             sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | (v3_pre_topc @ (sk_C @ sk_A) @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (((v3_pre_topc @ (sk_C @ sk_A) @ sk_A)
% 0.37/0.56        | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.37/0.56        | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.37/0.56        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['51', '58'])).
% 0.37/0.56  thf('60', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('61', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (((v3_pre_topc @ (sk_C @ sk_A) @ sk_A)
% 0.37/0.56        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (~ (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56          sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('64', plain, ((v3_pre_topc @ (sk_C @ sk_A) @ sk_A)),
% 0.37/0.56      inference('clc', [status(thm)], ['62', '63'])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      ((v3_pre_topc @ 
% 0.37/0.56        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ (sk_C @ sk_A)) @ 
% 0.37/0.56        sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['50', '64'])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (v3_pre_topc @ 
% 0.37/0.56             (k4_subset_1 @ (u1_struct_0 @ X6) @ (sk_B @ X6) @ (sk_C @ X6)) @ 
% 0.37/0.56             X6)
% 0.37/0.56          | ~ (v3_pre_topc @ 
% 0.37/0.56               (k9_subset_1 @ (u1_struct_0 @ X6) @ (sk_B @ X6) @ (sk_C @ X6)) @ 
% 0.37/0.56               X6)
% 0.37/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (v3_pre_topc @ X7 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X7 @ X6)
% 0.37/0.56          | ~ (v3_pre_topc @ X8 @ X6)
% 0.37/0.56          | ~ (v2_tex_2 @ X8 @ X6)
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X6) @ X7 @ X8) @ X6)
% 0.37/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.56          | ~ (l1_pre_topc @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t30_tex_2])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ X0) @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X1 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (v3_pre_topc @ 
% 0.37/0.56               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ 
% 0.37/0.56                (sk_C @ sk_A)) @ 
% 0.37/0.56               sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.56  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ X0) @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X1 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (v3_pre_topc @ 
% 0.37/0.56               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ 
% 0.37/0.56                (sk_C @ sk_A)) @ 
% 0.37/0.56               sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['67', '68'])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('clc', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('clc', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf(t38_tops_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56               ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.37/0.56                 ( v3_pre_topc @
% 0.37/0.56                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.37/0.56          | ~ (v3_pre_topc @ X3 @ X4)
% 0.37/0.56          | ~ (v3_pre_topc @ X5 @ X4)
% 0.37/0.56          | (v3_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X4) @ X3 @ X5) @ X4)
% 0.37/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.37/0.56          | ~ (l1_pre_topc @ X4)
% 0.37/0.56          | ~ (v2_pre_topc @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [t38_tops_1])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v3_pre_topc @ 
% 0.37/0.56             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ X0) @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.56  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('76', plain, ((v3_pre_topc @ (sk_B @ sk_A) @ sk_A)),
% 0.37/0.56      inference('clc', [status(thm)], ['46', '47'])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v3_pre_topc @ 
% 0.37/0.56             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ X0) @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.37/0.56  thf('78', plain,
% 0.37/0.56      ((~ (v3_pre_topc @ (sk_C @ sk_A) @ sk_A)
% 0.37/0.56        | (v3_pre_topc @ 
% 0.37/0.56           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ (sk_C @ sk_A)) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['70', '77'])).
% 0.37/0.56  thf('79', plain, ((v3_pre_topc @ (sk_C @ sk_A) @ sk_A)),
% 0.37/0.56      inference('clc', [status(thm)], ['62', '63'])).
% 0.37/0.56  thf('80', plain,
% 0.37/0.56      ((v3_pre_topc @ 
% 0.37/0.56        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ (sk_C @ sk_A)) @ 
% 0.37/0.56        sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['78', '79'])).
% 0.37/0.56  thf('81', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ X0) @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X1 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['69', '80'])).
% 0.37/0.56  thf('82', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | ~ (v3_pre_topc @ sk_C_1 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1) @ 
% 0.37/0.56             sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '81'])).
% 0.37/0.56  thf('83', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('84', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('85', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.56          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1) @ 
% 0.37/0.56             sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.37/0.56  thf('86', plain,
% 0.37/0.56      (((v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56         sk_A)
% 0.37/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.37/0.56        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '85'])).
% 0.37/0.56  thf('87', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('88', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('89', plain,
% 0.37/0.56      ((v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.37/0.56        sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.37/0.56  thf('90', plain, ($false), inference('demod', [status(thm)], ['0', '89'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
