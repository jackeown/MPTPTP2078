%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4gVBcv4yr0

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:28 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 576 expanded)
%              Number of leaves         :   28 ( 183 expanded)
%              Depth                    :   22
%              Number of atoms          :  861 (5332 expanded)
%              Number of equality atoms :   22 (  75 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tex_2,axiom,(
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
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( sk_C @ X20 @ X21 ) @ X20 )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ X10 @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( sk_B_1
      = ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(rc1_connsp_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X23 )
       != ( sk_C @ X20 @ X21 ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
       != ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
       != ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( sk_B @ sk_A ) )
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('28',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc1_connsp_1])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ X10 @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_1 )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_1 )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( sk_B @ sk_A ) )
    | ( sk_B_1
      = ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('45',plain,(
    r1_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('46',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ X10 @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ X0 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ X0 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_B_1 @ ( sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('52',plain,
    ( ( r1_tarski @ sk_B_1 @ ( sk_B @ sk_A ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ sk_B_1 @ ( sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_B_1
    = ( sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('58',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,
    ( sk_B_1
    = ( sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','54'])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('65',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_1 )
      = ( k3_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('69',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ X10 @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( sk_B_1
    = ( sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','54'])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','80'])).

thf('82',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( sk_B_1
      = ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( sk_B_1
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','55','62','63','66','85'])).

thf('87',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    sk_B_1
 != ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( r1_tarski @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','88'])).

thf('90',plain,(
    r2_hidden @ ( sk_D @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['15','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('92',plain,(
    $false ),
    inference('sup-',[status(thm)],['90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4gVBcv4yr0
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:05:14 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 310 iterations in 0.194s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.66  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(d10_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.66      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.66  thf(t3_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X11 : $i, X13 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('3', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf(t35_tex_2, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( v1_xboole_0 @ B ) & 
% 0.45/0.66             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.66            ( l1_pre_topc @ A ) ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( ( v1_xboole_0 @ B ) & 
% 0.45/0.66                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(d5_tex_2, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v2_tex_2 @ B @ A ) <=>
% 0.45/0.66             ( ![C:$i]:
% 0.45/0.66               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.45/0.66                      ( ![D:$i]:
% 0.45/0.66                        ( ( m1_subset_1 @
% 0.45/0.66                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.66                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.45/0.66                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X20 : $i, X21 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.66          | (r1_tarski @ (sk_C @ X20 @ X21) @ X20)
% 0.45/0.66          | (v2_tex_2 @ X20 @ X21)
% 0.45/0.66          | ~ (l1_pre_topc @ X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.45/0.66        | (r1_tarski @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.45/0.66        | (r1_tarski @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf('9', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('10', plain, ((r1_tarski @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.45/0.66      inference('clc', [status(thm)], ['8', '9'])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X11 : $i, X13 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf(t7_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66       ( ![C:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66           ( ( ![D:$i]:
% 0.45/0.66               ( ( m1_subset_1 @ D @ A ) =>
% 0.45/0.66                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.45/0.66             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.45/0.66          | (r1_tarski @ X10 @ X8)
% 0.45/0.66          | (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 0.45/0.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.45/0.66          | (r2_hidden @ (sk_D @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_B_1) @ X0)
% 0.45/0.66          | (r1_tarski @ X0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (((r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.45/0.66        | (r2_hidden @ (sk_D @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_B_1) @ 
% 0.45/0.66           sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '14'])).
% 0.45/0.66  thf('16', plain, ((r1_tarski @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.45/0.66      inference('clc', [status(thm)], ['8', '9'])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i, X2 : $i]:
% 0.45/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      ((~ (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.45/0.66        | ((sk_B_1) = (sk_C @ sk_B_1 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.66  thf(rc1_connsp_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ?[B:$i]:
% 0.45/0.66         ( ( v1_xboole_0 @ B ) & 
% 0.45/0.66           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X19 : $i]:
% 0.45/0.66         ((m1_subset_1 @ (sk_B @ X19) @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.66          | ~ (l1_pre_topc @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.66          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.45/0.66          | ~ (v3_pre_topc @ X23 @ X21)
% 0.45/0.66          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X23)
% 0.45/0.66              != (sk_C @ X20 @ X21))
% 0.45/0.66          | (v2_tex_2 @ X20 @ X21)
% 0.45/0.66          | ~ (l1_pre_topc @ X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ sk_A)
% 0.45/0.66          | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.45/0.66          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 0.45/0.66              != (sk_C @ sk_B_1 @ sk_A))
% 0.45/0.66          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.45/0.66          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 0.45/0.66              != (sk_C @ sk_B_1 @ sk_A))
% 0.45/0.66          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ~ (v3_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.45/0.66        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (sk_B @ sk_A))
% 0.45/0.66            != (sk_C @ sk_B_1 @ sk_A))
% 0.45/0.66        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['19', '24'])).
% 0.45/0.66  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X19 : $i]: ((v1_xboole_0 @ (sk_B @ X19)) | ~ (l1_pre_topc @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X19 : $i]:
% 0.45/0.66         ((m1_subset_1 @ (sk_B @ X19) @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.66          | ~ (l1_pre_topc @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [rc1_connsp_1])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.45/0.66          | (r1_tarski @ X10 @ X8)
% 0.45/0.66          | (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 0.45/0.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.45/0.66          | (r1_tarski @ X0 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | (r1_tarski @ (sk_B @ sk_A) @ sk_B_1)
% 0.45/0.66        | (r2_hidden @ 
% 0.45/0.66           (sk_D @ sk_B_1 @ (sk_B @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.66           (sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['28', '31'])).
% 0.45/0.66  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_1)
% 0.45/0.66        | (r2_hidden @ 
% 0.45/0.66           (sk_D @ sk_B_1 @ (sk_B @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.66           (sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.45/0.66  thf('35', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf(t5_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.66          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X14 @ X15)
% 0.45/0.66          | ~ (v1_xboole_0 @ X16)
% 0.45/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_1) | ~ (v1_xboole_0 @ (sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['34', '37'])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (sk_B @ sk_A) @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '38'])).
% 0.45/0.66  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('41', plain, ((r1_tarski @ (sk_B @ sk_A) @ sk_B_1)),
% 0.45/0.66      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X0 : $i, X2 : $i]:
% 0.45/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      ((~ (r1_tarski @ sk_B_1 @ (sk_B @ sk_A)) | ((sk_B_1) = (sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.66  thf('44', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf('45', plain, ((r1_tarski @ (sk_B @ sk_A) @ sk_B_1)),
% 0.45/0.66      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X11 : $i, X13 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('47', plain, ((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.45/0.66          | (r1_tarski @ X10 @ X8)
% 0.45/0.66          | (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 0.45/0.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.45/0.66          | (r2_hidden @ (sk_D @ (sk_B @ sk_A) @ X0 @ sk_B_1) @ X0)
% 0.45/0.66          | (r1_tarski @ X0 @ (sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (((r1_tarski @ sk_B_1 @ (sk_B @ sk_A))
% 0.45/0.66        | (r2_hidden @ (sk_D @ (sk_B @ sk_A) @ sk_B_1 @ sk_B_1) @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['44', '49'])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      (((r1_tarski @ sk_B_1 @ (sk_B @ sk_A)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.66  thf('53', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('54', plain, ((r1_tarski @ sk_B_1 @ (sk_B @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('55', plain, (((sk_B_1) = (sk_B @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['43', '54'])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc1_tops_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.66          | (v3_pre_topc @ X17 @ X18)
% 0.45/0.66          | ~ (v1_xboole_0 @ X17)
% 0.45/0.66          | ~ (l1_pre_topc @ X18)
% 0.45/0.66          | ~ (v2_pre_topc @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ~ (v1_xboole_0 @ sk_B_1)
% 0.45/0.66        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.66  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('61', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('62', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.45/0.66      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.45/0.66  thf('63', plain, (((sk_B_1) = (sk_B @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['43', '54'])).
% 0.45/0.66  thf('64', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k9_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.66         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.45/0.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B_1)
% 0.45/0.66           = (k3_xboole_0 @ X0 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.66  thf('67', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf(t17_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.45/0.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      (![X11 : $i, X13 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('70', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.45/0.66          | (r1_tarski @ X10 @ X8)
% 0.45/0.66          | (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 0.45/0.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.45/0.66          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X2 @ X0) @ X2)
% 0.45/0.66          | (r1_tarski @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['70', '71'])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.66          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X0) @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['67', '72'])).
% 0.45/0.66  thf('74', plain, ((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.66  thf('75', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X14 @ X15)
% 0.45/0.66          | ~ (v1_xboole_0 @ X16)
% 0.45/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.66  thf('76', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.66  thf('77', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.45/0.66  thf('79', plain, (((sk_B_1) = (sk_B @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['43', '54'])).
% 0.45/0.66  thf('80', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.45/0.66      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.66  thf('81', plain,
% 0.45/0.66      (![X0 : $i]: (r1_tarski @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['73', '80'])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.45/0.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      (![X0 : $i, X2 : $i]:
% 0.45/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.45/0.66          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['82', '83'])).
% 0.45/0.66  thf('85', plain, (![X0 : $i]: ((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['81', '84'])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      ((((sk_B_1) != (sk_C @ sk_B_1 @ sk_A)) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)],
% 0.45/0.66                ['25', '26', '55', '62', '63', '66', '85'])).
% 0.45/0.66  thf('87', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('88', plain, (((sk_B_1) != (sk_C @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['86', '87'])).
% 0.45/0.66  thf('89', plain, (~ (r1_tarski @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['18', '88'])).
% 0.45/0.66  thf('90', plain,
% 0.45/0.66      ((r2_hidden @ (sk_D @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_B_1) @ sk_B_1)),
% 0.45/0.66      inference('clc', [status(thm)], ['15', '89'])).
% 0.45/0.66  thf('91', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.45/0.66      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.66  thf('92', plain, ($false), inference('sup-', [status(thm)], ['90', '91'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
