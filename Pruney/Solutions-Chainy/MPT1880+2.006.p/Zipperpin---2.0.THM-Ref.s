%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.acWDf9Xd6M

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:10 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 262 expanded)
%              Number of leaves         :   22 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  803 (3628 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t48_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v1_tops_1 @ B @ A )
                & ( v2_tex_2 @ B @ A ) )
             => ( v3_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 @ ( k2_pre_topc @ X12 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( v2_tex_2 @ ( sk_C @ X8 @ X9 ) @ X9 )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_tex_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( sk_C @ X8 @ X9 ) )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v1_tops_1 @ X3 @ X4 )
      | ( ( k2_pre_topc @ X4 @ X3 )
        = ( k2_struct_0 @ X4 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','30','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','20'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
      = ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v1_tops_1 @ X3 @ X4 )
      | ( ( k2_pre_topc @ X4 @ X3 )
        = ( k2_struct_0 @ X4 ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( v1_tops_1 @ C @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v1_tops_1 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( v1_tops_1 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    r1_tarski @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('59',plain,(
    v1_tops_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('61',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','44','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_B
    = ( sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( X8
       != ( sk_C @ X8 @ X9 ) )
      | ( v3_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v3_tex_2 @ sk_B @ sk_A )
    | ( sk_B
     != ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v3_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_B
 != ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.acWDf9Xd6M
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:31:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 59 iterations in 0.034s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.23/0.51  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.23/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.23/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.51  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(t48_tex_2, conjecture,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.23/0.51             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]:
% 0.23/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.51            ( l1_pre_topc @ A ) ) =>
% 0.23/0.51          ( ![B:$i]:
% 0.23/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51              ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.23/0.51                ( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t48_tex_2])).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(d7_tex_2, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( l1_pre_topc @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51           ( ( v3_tex_2 @ B @ A ) <=>
% 0.23/0.51             ( ( v2_tex_2 @ B @ A ) & 
% 0.23/0.51               ( ![C:$i]:
% 0.23/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.23/0.51                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X8 : $i, X9 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.23/0.51          | ~ (v2_tex_2 @ X8 @ X9)
% 0.23/0.51          | (m1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.23/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.23/0.51          | (v3_tex_2 @ X8 @ X9)
% 0.23/0.51          | ~ (l1_pre_topc @ X9))),
% 0.23/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.51        | (v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.51        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('5', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (((v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.51        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.23/0.51  thf('7', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf(t41_tex_2, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51           ( ( v2_tex_2 @ B @ A ) <=>
% 0.23/0.51             ( ![C:$i]:
% 0.23/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51                 ( ( r1_tarski @ C @ B ) =>
% 0.23/0.51                   ( ( k9_subset_1 @
% 0.23/0.51                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.23/0.51                     ( C ) ) ) ) ) ) ) ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.23/0.51          | ~ (v2_tex_2 @ X11 @ X12)
% 0.23/0.51          | ~ (r1_tarski @ X13 @ X11)
% 0.23/0.51          | ((k9_subset_1 @ (u1_struct_0 @ X12) @ X11 @ 
% 0.23/0.51              (k2_pre_topc @ X12 @ X13)) = (X13))
% 0.23/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.23/0.51          | ~ (l1_pre_topc @ X12)
% 0.23/0.51          | ~ (v2_pre_topc @ X12)
% 0.23/0.51          | (v2_struct_0 @ X12))),
% 0.23/0.51      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v2_struct_0 @ sk_A)
% 0.23/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.23/0.51          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.23/0.51          | ~ (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.51  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X8 : $i, X9 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.23/0.51          | ~ (v2_tex_2 @ X8 @ X9)
% 0.23/0.51          | (v2_tex_2 @ (sk_C @ X8 @ X9) @ X9)
% 0.23/0.51          | (v3_tex_2 @ X8 @ X9)
% 0.23/0.51          | ~ (l1_pre_topc @ X9))),
% 0.23/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.51        | (v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.51        | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.23/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('17', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (((v3_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.23/0.51  thf('19', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('20', plain, ((v2_tex_2 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.23/0.51      inference('clc', [status(thm)], ['18', '19'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v2_struct_0 @ sk_A)
% 0.23/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.23/0.51          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['10', '11', '12', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.23/0.51        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51            (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.23/0.51        | (v2_struct_0 @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['0', '21'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (![X8 : $i, X9 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.23/0.51          | ~ (v2_tex_2 @ X8 @ X9)
% 0.23/0.51          | (r1_tarski @ X8 @ (sk_C @ X8 @ X9))
% 0.23/0.51          | (v3_tex_2 @ X8 @ X9)
% 0.23/0.51          | ~ (l1_pre_topc @ X9))),
% 0.23/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.51        | (v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.51        | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.23/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.51  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('28', plain,
% 0.23/0.51      (((v3_tex_2 @ sk_B @ sk_A) | (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.23/0.51  thf('29', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('30', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.23/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.23/0.51  thf('31', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(d3_tops_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( l1_pre_topc @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51           ( ( v1_tops_1 @ B @ A ) <=>
% 0.23/0.51             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.23/0.51  thf('32', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.23/0.51          | ~ (v1_tops_1 @ X3 @ X4)
% 0.23/0.51          | ((k2_pre_topc @ X4 @ X3) = (k2_struct_0 @ X4))
% 0.23/0.51          | ~ (l1_pre_topc @ X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.23/0.51  thf('33', plain,
% 0.23/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.51        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.23/0.51        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.23/0.51  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('35', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('36', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.23/0.51  thf('37', plain,
% 0.23/0.51      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51          (k2_struct_0 @ sk_A)) = (sk_B))
% 0.23/0.51        | (v2_struct_0 @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['22', '30', '36'])).
% 0.23/0.51  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('39', plain,
% 0.23/0.51      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51         (k2_struct_0 @ sk_A)) = (sk_B))),
% 0.23/0.51      inference('clc', [status(thm)], ['37', '38'])).
% 0.23/0.51  thf('40', plain,
% 0.23/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf('41', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v2_struct_0 @ sk_A)
% 0.23/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.23/0.51          | ~ (r1_tarski @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['10', '11', '12', '20'])).
% 0.23/0.51  thf('42', plain,
% 0.23/0.51      ((~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.23/0.51        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51            (k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A))) = (sk_C @ sk_B @ sk_A))
% 0.23/0.51        | (v2_struct_0 @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.23/0.51  thf(d10_xboole_0, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.51  thf('43', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.51  thf('44', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.51      inference('simplify', [status(thm)], ['43'])).
% 0.23/0.51  thf('45', plain,
% 0.23/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf('46', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.23/0.51          | ~ (v1_tops_1 @ X3 @ X4)
% 0.23/0.51          | ((k2_pre_topc @ X4 @ X3) = (k2_struct_0 @ X4))
% 0.23/0.51          | ~ (l1_pre_topc @ X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.23/0.51  thf('47', plain,
% 0.23/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.51        | ((k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.23/0.51        | ~ (v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.23/0.51  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('49', plain,
% 0.23/0.51      ((((k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.23/0.51        | ~ (v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['47', '48'])).
% 0.23/0.51  thf('50', plain,
% 0.23/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf('51', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t79_tops_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( l1_pre_topc @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51           ( ![C:$i]:
% 0.23/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.51               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.23/0.51                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.23/0.51  thf('52', plain,
% 0.23/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.23/0.51          | ~ (v1_tops_1 @ X5 @ X6)
% 0.23/0.51          | ~ (r1_tarski @ X5 @ X7)
% 0.23/0.51          | (v1_tops_1 @ X7 @ X6)
% 0.23/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.23/0.51          | ~ (l1_pre_topc @ X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [t79_tops_1])).
% 0.23/0.51  thf('53', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (l1_pre_topc @ sk_A)
% 0.23/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51          | (v1_tops_1 @ X0 @ sk_A)
% 0.23/0.51          | ~ (r1_tarski @ sk_B @ X0)
% 0.23/0.51          | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.23/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('55', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('56', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.51          | (v1_tops_1 @ X0 @ sk_A)
% 0.23/0.51          | ~ (r1_tarski @ sk_B @ X0))),
% 0.23/0.51      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.23/0.51  thf('57', plain,
% 0.23/0.51      ((~ (r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.23/0.51        | (v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['50', '56'])).
% 0.23/0.51  thf('58', plain, ((r1_tarski @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.23/0.51      inference('clc', [status(thm)], ['28', '29'])).
% 0.23/0.51  thf('59', plain, ((v1_tops_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.23/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.23/0.51  thf('60', plain,
% 0.23/0.51      (((k2_pre_topc @ sk_A @ (sk_C @ sk_B @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['49', '59'])).
% 0.23/0.51  thf('61', plain,
% 0.23/0.51      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51          (k2_struct_0 @ sk_A)) = (sk_C @ sk_B @ sk_A))
% 0.23/0.51        | (v2_struct_0 @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['42', '44', '60'])).
% 0.23/0.51  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('63', plain,
% 0.23/0.51      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A) @ 
% 0.23/0.51         (k2_struct_0 @ sk_A)) = (sk_C @ sk_B @ sk_A))),
% 0.23/0.51      inference('clc', [status(thm)], ['61', '62'])).
% 0.23/0.51  thf('64', plain, (((sk_B) = (sk_C @ sk_B @ sk_A))),
% 0.23/0.51      inference('sup+', [status(thm)], ['39', '63'])).
% 0.23/0.51  thf('65', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('66', plain,
% 0.23/0.51      (![X8 : $i, X9 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.23/0.51          | ~ (v2_tex_2 @ X8 @ X9)
% 0.23/0.51          | ((X8) != (sk_C @ X8 @ X9))
% 0.23/0.51          | (v3_tex_2 @ X8 @ X9)
% 0.23/0.51          | ~ (l1_pre_topc @ X9))),
% 0.23/0.51      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.23/0.51  thf('67', plain,
% 0.23/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.51        | (v3_tex_2 @ sk_B @ sk_A)
% 0.23/0.51        | ((sk_B) != (sk_C @ sk_B @ sk_A))
% 0.23/0.51        | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['65', '66'])).
% 0.23/0.51  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('69', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('70', plain,
% 0.23/0.51      (((v3_tex_2 @ sk_B @ sk_A) | ((sk_B) != (sk_C @ sk_B @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.23/0.51  thf('71', plain, (~ (v3_tex_2 @ sk_B @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('72', plain, (((sk_B) != (sk_C @ sk_B @ sk_A))),
% 0.23/0.51      inference('clc', [status(thm)], ['70', '71'])).
% 0.23/0.51  thf('73', plain, ($false),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['64', '72'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
