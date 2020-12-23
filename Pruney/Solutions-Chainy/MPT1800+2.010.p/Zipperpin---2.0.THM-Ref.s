%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z1iMuZIQdh

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:56 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  244 (1195 expanded)
%              Number of leaves         :   36 ( 348 expanded)
%              Depth                    :   24
%              Number of atoms          : 2032 (18483 expanded)
%              Number of equality atoms :   82 ( 639 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t116_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( v1_tsep_1 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k8_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( ( v1_tsep_1 @ B @ A )
                & ( m1_pre_topc @ B @ A ) )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k8_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_tmap_1])).

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tsep_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( ( sk_C @ X11 @ X12 )
        = ( u1_struct_0 @ X11 ) )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ( v3_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('14',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( v3_pre_topc @ ( sk_C @ X11 @ X12 ) @ X12 )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('22',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['19','27'])).

thf('29',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('32',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t114_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
                    = ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X23 @ X22 ) )
        = ( k5_tmap_1 @ X23 @ X24 ) )
      | ( X24
       != ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X23 @ X22 ) )
        = ( k5_tmap_1 @ X23 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ( X13
       != ( u1_struct_0 @ X11 ) )
      | ( v3_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('62',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t103_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
          <=> ( ( u1_pre_topc @ A )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r2_hidden @ X18 @ ( u1_pre_topc @ X19 ) )
      | ( ( u1_pre_topc @ X19 )
        = ( k5_tmap_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['50','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X23 @ X22 ) )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['84','85'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('88',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('90',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('91',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('99',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','96','104'])).

thf('106',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['76','105'])).

thf('107',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('108',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','34','109'])).

thf('111',plain,(
    ~ ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['30','110'])).

thf('112',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('113',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_pre_topc @ X19 )
       != ( k5_tmap_1 @ X19 @ X18 ) )
      | ( r2_hidden @ X18 @ ( u1_pre_topc @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('121',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t35_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf('123',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m2_connsp_2 @ ( k2_struct_0 @ X10 ) @ X10 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t35_connsp_2])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(dt_m2_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('131',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m2_connsp_2 @ X8 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_connsp_2])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('137',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X20 ) )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('145',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('147',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('148',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('155',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('156',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['145','153','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('164',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X21 @ X20 ) )
        = ( k5_tmap_1 @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('169',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r2_hidden @ X18 @ ( u1_pre_topc @ X19 ) )
      | ( ( u1_pre_topc @ X19 )
        = ( k5_tmap_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('174',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('175',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['175','176'])).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('178',plain,(
    ! [X5: $i] :
      ( ( ( k1_tops_1 @ X5 @ ( k2_struct_0 @ X5 ) )
        = ( k2_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf('179',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('180',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X3 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('181',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['178','184'])).

thf('186',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['177','188'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['170','171','172','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['165','166','167','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','195'])).

thf('197',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('198',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('200',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('202',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['31','34','109','201'])).

thf('203',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['200','202'])).

thf('204',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','203'])).

thf('205',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    $false ),
    inference(demod,[status(thm)],['111','205'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z1iMuZIQdh
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 246 iterations in 0.111s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.37/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.57  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.37/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.57  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.37/0.57  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.37/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.57  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.37/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.37/0.57  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.57  thf(t116_tmap_1, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.57           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.37/0.57             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.57               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.57            ( l1_pre_topc @ A ) ) =>
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.57              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.37/0.57                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.57                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.37/0.57  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(d1_tsep_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.57           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.37/0.57             ( ![C:$i]:
% 0.37/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X11 @ X12)
% 0.37/0.57          | ((sk_C @ X11 @ X12) = (u1_struct_0 @ X11))
% 0.37/0.57          | (v1_tsep_1 @ X11 @ X12)
% 0.37/0.57          | ~ (l1_pre_topc @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.57  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.37/0.57        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.37/0.57         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.37/0.57  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X11 @ X12)
% 0.37/0.57          | (m1_subset_1 @ (sk_C @ X11 @ X12) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.57          | (v1_tsep_1 @ X11 @ X12)
% 0.37/0.57          | ~ (l1_pre_topc @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.57  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf(d5_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( v3_pre_topc @ B @ A ) <=>
% 0.37/0.57             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.37/0.57          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.37/0.57          | (v3_pre_topc @ X1 @ X2)
% 0.37/0.57          | ~ (l1_pre_topc @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.57        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.57  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.57        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57         | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.37/0.57         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.37/0.57         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.57         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.37/0.57         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X11 @ X12)
% 0.37/0.57          | ~ (v3_pre_topc @ (sk_C @ X11 @ X12) @ X12)
% 0.37/0.57          | (v1_tsep_1 @ X11 @ X12)
% 0.37/0.57          | ~ (l1_pre_topc @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.57         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.37/0.57         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['25', '26'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      ((((v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57         | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))
% 0.37/0.57         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['19', '27'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['28', '29'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.37/0.57       ~
% 0.37/0.57       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.37/0.57       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('34', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t1_tsep_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.57           ( m1_subset_1 @
% 0.37/0.57             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (![X25 : $i, X26 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X25 @ X26)
% 0.37/0.57          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.37/0.57          | ~ (l1_pre_topc @ X26))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf(t114_tmap_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.57           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.37/0.57             ( ![C:$i]:
% 0.37/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.37/0.57                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.37/0.57                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.57         ((v2_struct_0 @ X22)
% 0.37/0.57          | ~ (m1_pre_topc @ X22 @ X23)
% 0.37/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.57          | ((u1_pre_topc @ (k8_tmap_1 @ X23 @ X22)) = (k5_tmap_1 @ X23 @ X24))
% 0.37/0.57          | ((X24) != (u1_struct_0 @ X22))
% 0.37/0.57          | ~ (l1_pre_topc @ X23)
% 0.37/0.57          | ~ (v2_pre_topc @ X23)
% 0.37/0.57          | (v2_struct_0 @ X23))),
% 0.37/0.57      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i]:
% 0.37/0.57         ((v2_struct_0 @ X23)
% 0.37/0.57          | ~ (v2_pre_topc @ X23)
% 0.37/0.57          | ~ (l1_pre_topc @ X23)
% 0.37/0.57          | ((u1_pre_topc @ (k8_tmap_1 @ X23 @ X22))
% 0.37/0.57              = (k5_tmap_1 @ X23 @ (u1_struct_0 @ X22)))
% 0.37/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.37/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.57          | ~ (m1_pre_topc @ X22 @ X23)
% 0.37/0.57          | (v2_struct_0 @ X22))),
% 0.37/0.57      inference('simplify', [status(thm)], ['40'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_B)
% 0.37/0.57        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.37/0.57        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | (v2_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['39', '41'])).
% 0.37/0.57  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_B)
% 0.37/0.57        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.37/0.57        | (v2_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.37/0.57  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('clc', [status(thm)], ['46', '47'])).
% 0.37/0.57  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('clc', [status(thm)], ['48', '49'])).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['51'])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('54', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X11 @ X12)
% 0.37/0.57          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.37/0.57          | ((X13) != (u1_struct_0 @ X11))
% 0.37/0.57          | (v3_pre_topc @ X13 @ X12)
% 0.37/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.57          | ~ (l1_pre_topc @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.37/0.57  thf('55', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X12)
% 0.37/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.37/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.57          | (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.37/0.57          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.37/0.57          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.37/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.37/0.57  thf('56', plain,
% 0.37/0.57      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.37/0.57        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['53', '55'])).
% 0.37/0.57  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.37/0.57        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.37/0.57         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['52', '59'])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      (![X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.37/0.57          | ~ (v3_pre_topc @ X1 @ X2)
% 0.37/0.57          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.37/0.57          | ~ (l1_pre_topc @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.37/0.57  thf('63', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.57  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('65', plain,
% 0.37/0.57      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['63', '64'])).
% 0.37/0.57  thf('66', plain,
% 0.37/0.57      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['60', '65'])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf(t103_tmap_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.37/0.57             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      (![X18 : $i, X19 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.57          | ~ (r2_hidden @ X18 @ (u1_pre_topc @ X19))
% 0.37/0.57          | ((u1_pre_topc @ X19) = (k5_tmap_1 @ X19 @ X18))
% 0.37/0.57          | ~ (l1_pre_topc @ X19)
% 0.37/0.57          | ~ (v2_pre_topc @ X19)
% 0.37/0.57          | (v2_struct_0 @ X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.37/0.57        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.57  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('72', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.37/0.57        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.37/0.57  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('74', plain,
% 0.37/0.57      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('clc', [status(thm)], ['72', '73'])).
% 0.37/0.57  thf('75', plain,
% 0.37/0.57      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.37/0.57         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['66', '74'])).
% 0.37/0.57  thf('76', plain,
% 0.37/0.57      ((((u1_pre_topc @ sk_A) = (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['50', '75'])).
% 0.37/0.57  thf('77', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('78', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i]:
% 0.37/0.57         ((v2_struct_0 @ X22)
% 0.37/0.57          | ~ (m1_pre_topc @ X22 @ X23)
% 0.37/0.57          | ((u1_struct_0 @ (k8_tmap_1 @ X23 @ X22)) = (u1_struct_0 @ X23))
% 0.37/0.57          | ~ (l1_pre_topc @ X23)
% 0.37/0.57          | ~ (v2_pre_topc @ X23)
% 0.37/0.57          | (v2_struct_0 @ X23))),
% 0.37/0.57      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.37/0.57  thf('79', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | (v2_struct_0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['77', '78'])).
% 0.37/0.57  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('82', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | (v2_struct_0 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.37/0.57  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('84', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_B)
% 0.37/0.57        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['82', '83'])).
% 0.37/0.57  thf('85', plain, (~ (v2_struct_0 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('86', plain,
% 0.37/0.57      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('clc', [status(thm)], ['84', '85'])).
% 0.37/0.57  thf(abstractness_v1_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ( v1_pre_topc @ A ) =>
% 0.37/0.57         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.37/0.57  thf('87', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (v1_pre_topc @ X0)
% 0.37/0.57          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.37/0.57  thf('88', plain,
% 0.37/0.57      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.37/0.57          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.57             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.37/0.57        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['86', '87'])).
% 0.37/0.57  thf('89', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(dt_k8_tmap_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.57         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.57       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.37/0.57         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.37/0.57         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.37/0.57  thf('90', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X16)
% 0.37/0.57          | ~ (v2_pre_topc @ X16)
% 0.37/0.57          | (v2_struct_0 @ X16)
% 0.37/0.57          | ~ (m1_pre_topc @ X17 @ X16)
% 0.37/0.57          | (l1_pre_topc @ (k8_tmap_1 @ X16 @ X17)))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.37/0.57  thf('91', plain,
% 0.37/0.57      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57        | (v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['89', '90'])).
% 0.37/0.57  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('94', plain,
% 0.37/0.57      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.37/0.57  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('96', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.37/0.57      inference('clc', [status(thm)], ['94', '95'])).
% 0.37/0.57  thf('97', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('98', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X16)
% 0.37/0.57          | ~ (v2_pre_topc @ X16)
% 0.37/0.57          | (v2_struct_0 @ X16)
% 0.37/0.57          | ~ (m1_pre_topc @ X17 @ X16)
% 0.37/0.57          | (v1_pre_topc @ (k8_tmap_1 @ X16 @ X17)))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.37/0.57  thf('99', plain,
% 0.37/0.57      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57        | (v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['97', '98'])).
% 0.37/0.57  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('102', plain,
% 0.37/0.57      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.37/0.57  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('104', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.37/0.57      inference('clc', [status(thm)], ['102', '103'])).
% 0.37/0.57  thf('105', plain,
% 0.37/0.57      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.37/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.57            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('demod', [status(thm)], ['88', '96', '104'])).
% 0.37/0.57  thf('106', plain,
% 0.37/0.57      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.37/0.57          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.37/0.57         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['76', '105'])).
% 0.37/0.57  thf('107', plain,
% 0.37/0.57      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (~
% 0.37/0.57             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('split', [status(esa)], ['5'])).
% 0.37/0.57  thf('108', plain,
% 0.37/0.57      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (~
% 0.37/0.57             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.37/0.57             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['106', '107'])).
% 0.37/0.57  thf('109', plain,
% 0.37/0.57      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.37/0.57       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('simplify', [status(thm)], ['108'])).
% 0.37/0.57  thf('110', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['31', '34', '109'])).
% 0.37/0.57  thf('111', plain,
% 0.37/0.57      (~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['30', '110'])).
% 0.37/0.57  thf('112', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('113', plain,
% 0.37/0.57      (![X18 : $i, X19 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.57          | ((u1_pre_topc @ X19) != (k5_tmap_1 @ X19 @ X18))
% 0.37/0.57          | (r2_hidden @ X18 @ (u1_pre_topc @ X19))
% 0.37/0.57          | ~ (l1_pre_topc @ X19)
% 0.37/0.57          | ~ (v2_pre_topc @ X19)
% 0.37/0.57          | (v2_struct_0 @ X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.37/0.57  thf('114', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.37/0.57  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('117', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.37/0.57  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('119', plain,
% 0.37/0.57      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.37/0.57        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['117', '118'])).
% 0.37/0.57  thf('120', plain,
% 0.37/0.57      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.37/0.57         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('clc', [status(thm)], ['48', '49'])).
% 0.37/0.57  thf('121', plain,
% 0.37/0.57      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.57        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['119', '120'])).
% 0.37/0.57  thf('122', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf(t35_connsp_2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.37/0.57  thf('123', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.37/0.57          | (m2_connsp_2 @ (k2_struct_0 @ X10) @ X10 @ X9)
% 0.37/0.57          | ~ (l1_pre_topc @ X10)
% 0.37/0.57          | ~ (v2_pre_topc @ X10)
% 0.37/0.57          | (v2_struct_0 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t35_connsp_2])).
% 0.37/0.57  thf('124', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['122', '123'])).
% 0.37/0.57  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('127', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.37/0.57  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('129', plain,
% 0.37/0.57      ((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ (u1_struct_0 @ sk_B))),
% 0.37/0.57      inference('clc', [status(thm)], ['127', '128'])).
% 0.37/0.57  thf('130', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf(dt_m2_connsp_2, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.37/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57       ( ![C:$i]:
% 0.37/0.57         ( ( m2_connsp_2 @ C @ A @ B ) =>
% 0.37/0.57           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('131', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X6)
% 0.37/0.57          | ~ (v2_pre_topc @ X6)
% 0.37/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.57          | (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.57          | ~ (m2_connsp_2 @ X8 @ X6 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_m2_connsp_2])).
% 0.37/0.57  thf('132', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m2_connsp_2 @ X0 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.37/0.57          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57          | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['130', '131'])).
% 0.37/0.57  thf('133', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('135', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m2_connsp_2 @ X0 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.37/0.57          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.37/0.57  thf('136', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['129', '135'])).
% 0.37/0.57  thf(t104_tmap_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.37/0.57             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.57  thf('137', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.57          | ((u1_struct_0 @ (k6_tmap_1 @ X21 @ X20)) = (u1_struct_0 @ X21))
% 0.37/0.57          | ~ (l1_pre_topc @ X21)
% 0.37/0.57          | ~ (v2_pre_topc @ X21)
% 0.37/0.57          | (v2_struct_0 @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.37/0.57  thf('138', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57            = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['136', '137'])).
% 0.37/0.57  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('141', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57            = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.37/0.57  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('143', plain,
% 0.37/0.57      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57         = (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('clc', [status(thm)], ['141', '142'])).
% 0.37/0.57  thf('144', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (v1_pre_topc @ X0)
% 0.37/0.57          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.37/0.57  thf('145', plain,
% 0.37/0.57      ((((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.37/0.57          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.57             (u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))))
% 0.37/0.57        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['143', '144'])).
% 0.37/0.57  thf('146', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['129', '135'])).
% 0.37/0.57  thf(dt_k6_tmap_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.57         ( l1_pre_topc @ A ) & 
% 0.37/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.37/0.57         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.37/0.57         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.37/0.57  thf('147', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X14)
% 0.37/0.57          | ~ (v2_pre_topc @ X14)
% 0.37/0.57          | (v2_struct_0 @ X14)
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.57          | (l1_pre_topc @ (k6_tmap_1 @ X14 @ X15)))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.37/0.57  thf('148', plain,
% 0.37/0.57      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57        | (v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['146', '147'])).
% 0.37/0.57  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('151', plain,
% 0.37/0.57      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57        | (v2_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.37/0.57  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('153', plain,
% 0.37/0.57      ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['151', '152'])).
% 0.37/0.57  thf('154', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['129', '135'])).
% 0.37/0.57  thf('155', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X14)
% 0.37/0.57          | ~ (v2_pre_topc @ X14)
% 0.37/0.57          | (v2_struct_0 @ X14)
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.57          | (v1_pre_topc @ (k6_tmap_1 @ X14 @ X15)))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.37/0.57  thf('156', plain,
% 0.37/0.57      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57        | (v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['154', '155'])).
% 0.37/0.57  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('159', plain,
% 0.37/0.57      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57        | (v2_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['156', '157', '158'])).
% 0.37/0.57  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('161', plain,
% 0.37/0.57      ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['159', '160'])).
% 0.37/0.57  thf('162', plain,
% 0.37/0.57      (((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.37/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.57            (u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.57      inference('demod', [status(thm)], ['145', '153', '161'])).
% 0.37/0.57  thf('163', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['129', '135'])).
% 0.37/0.57  thf('164', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.57          | ((u1_pre_topc @ (k6_tmap_1 @ X21 @ X20)) = (k5_tmap_1 @ X21 @ X20))
% 0.37/0.57          | ~ (l1_pre_topc @ X21)
% 0.37/0.57          | ~ (v2_pre_topc @ X21)
% 0.37/0.57          | (v2_struct_0 @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.37/0.57  thf('165', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57            = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['163', '164'])).
% 0.37/0.57  thf('166', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('168', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['129', '135'])).
% 0.37/0.57  thf('169', plain,
% 0.37/0.57      (![X18 : $i, X19 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.57          | ~ (r2_hidden @ X18 @ (u1_pre_topc @ X19))
% 0.37/0.57          | ((u1_pre_topc @ X19) = (k5_tmap_1 @ X19 @ X18))
% 0.37/0.57          | ~ (l1_pre_topc @ X19)
% 0.37/0.57          | ~ (v2_pre_topc @ X19)
% 0.37/0.57          | (v2_struct_0 @ X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.37/0.57  thf('170', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['168', '169'])).
% 0.37/0.57  thf('171', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('173', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['129', '135'])).
% 0.37/0.57  thf('174', plain,
% 0.37/0.57      (![X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.37/0.57          | ~ (v3_pre_topc @ X1 @ X2)
% 0.37/0.57          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.37/0.57          | ~ (l1_pre_topc @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.37/0.57  thf('175', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['173', '174'])).
% 0.37/0.57  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('177', plain,
% 0.37/0.57      (((r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['175', '176'])).
% 0.37/0.57  thf(t43_tops_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.37/0.57  thf('178', plain,
% 0.37/0.57      (![X5 : $i]:
% 0.37/0.57         (((k1_tops_1 @ X5 @ (k2_struct_0 @ X5)) = (k2_struct_0 @ X5))
% 0.37/0.57          | ~ (l1_pre_topc @ X5)
% 0.37/0.57          | ~ (v2_pre_topc @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.37/0.57  thf('179', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['129', '135'])).
% 0.37/0.57  thf(fc9_tops_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.37/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.37/0.57  thf('180', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X3)
% 0.37/0.57          | ~ (v2_pre_topc @ X3)
% 0.37/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.37/0.57          | (v3_pre_topc @ (k1_tops_1 @ X3 @ X4) @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.37/0.57  thf('181', plain,
% 0.37/0.57      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['179', '180'])).
% 0.37/0.57  thf('182', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('183', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('184', plain,
% 0.37/0.57      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['181', '182', '183'])).
% 0.37/0.57  thf('185', plain,
% 0.37/0.57      (((v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup+', [status(thm)], ['178', '184'])).
% 0.37/0.57  thf('186', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('188', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.37/0.57  thf('189', plain,
% 0.37/0.57      ((r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['177', '188'])).
% 0.37/0.57  thf('190', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['170', '171', '172', '189'])).
% 0.37/0.57  thf('191', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('192', plain,
% 0.37/0.57      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['190', '191'])).
% 0.37/0.57  thf('193', plain,
% 0.37/0.57      (((v2_struct_0 @ sk_A)
% 0.37/0.57        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57            = (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['165', '166', '167', '192'])).
% 0.37/0.57  thf('194', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('195', plain,
% 0.37/0.57      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57         = (u1_pre_topc @ sk_A))),
% 0.37/0.57      inference('clc', [status(thm)], ['193', '194'])).
% 0.37/0.57  thf('196', plain,
% 0.37/0.57      (((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.37/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['162', '195'])).
% 0.37/0.57  thf('197', plain,
% 0.37/0.57      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('split', [status(esa)], ['51'])).
% 0.37/0.57  thf('198', plain,
% 0.37/0.57      ((((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['196', '197'])).
% 0.37/0.57  thf('199', plain,
% 0.37/0.57      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.57         = (u1_pre_topc @ sk_A))),
% 0.37/0.57      inference('clc', [status(thm)], ['193', '194'])).
% 0.37/0.57  thf('200', plain,
% 0.37/0.57      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A)))
% 0.37/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['198', '199'])).
% 0.37/0.57  thf('201', plain,
% 0.37/0.57      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.37/0.57       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.37/0.57      inference('split', [status(esa)], ['51'])).
% 0.37/0.57  thf('202', plain,
% 0.37/0.57      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['31', '34', '109', '201'])).
% 0.37/0.57  thf('203', plain,
% 0.37/0.57      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A))),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['200', '202'])).
% 0.37/0.57  thf('204', plain,
% 0.37/0.57      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.37/0.57        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['121', '203'])).
% 0.37/0.57  thf('205', plain,
% 0.37/0.57      ((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.37/0.57      inference('simplify', [status(thm)], ['204'])).
% 0.37/0.57  thf('206', plain, ($false), inference('demod', [status(thm)], ['111', '205'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
