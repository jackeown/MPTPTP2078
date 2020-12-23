%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.znxgCkQlIf

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:56 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 902 expanded)
%              Number of leaves         :   36 ( 264 expanded)
%              Depth                    :   21
%              Number of atoms          : 1898 (13987 expanded)
%              Number of equality atoms :   79 ( 507 expanded)
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

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

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

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ( ( u1_pre_topc @ X17 )
        = ( k5_tmap_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X14 @ X15 ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X14 @ X15 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_pre_topc @ X17 )
       != ( k5_tmap_1 @ X17 @ X16 ) )
      | ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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

thf(t106_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf('137',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X21 ) @ ( u1_pre_topc @ X21 ) )
        = ( k6_tmap_1 @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('141',plain,(
    ! [X5: $i] :
      ( ( ( k1_tops_1 @ X5 @ ( k2_struct_0 @ X5 ) )
        = ( k2_struct_0 @ X5 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf('142',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('143',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X3 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('144',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['141','147'])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['138','139','140','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('156',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
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

thf('158',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X19 @ X18 ) )
        = ( k5_tmap_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('166',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ( ( u1_pre_topc @ X17 )
        = ( k5_tmap_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('171',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( u1_pre_topc @ X2 ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('172',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('176',plain,(
    r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['167','168','169','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['164','179'])).

thf('181',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['156','180'])).

thf('182',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('183',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['31','34','109','182'])).

thf('184',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['181','183'])).

thf('185',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','184'])).

thf('186',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    $false ),
    inference(demod,[status(thm)],['111','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.znxgCkQlIf
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:24:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 207 iterations in 0.170s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.46/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.63  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.46/0.63  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.46/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.63  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.46/0.63  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(t116_tmap_1, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.63           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.63             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.46/0.63               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.63            ( l1_pre_topc @ A ) ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.63              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.63                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.46/0.63                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.46/0.63  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d1_tsep_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.63           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.46/0.63             ( ![C:$i]:
% 0.46/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X11 : $i, X12 : $i]:
% 0.46/0.63         (~ (m1_pre_topc @ X11 @ X12)
% 0.46/0.63          | ((sk_C @ X11 @ X12) = (u1_struct_0 @ X11))
% 0.46/0.63          | (v1_tsep_1 @ X11 @ X12)
% 0.46/0.63          | ~ (l1_pre_topc @ X12))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.63  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.63          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.63        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['5'])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.46/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.46/0.63  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X11 : $i, X12 : $i]:
% 0.46/0.63         (~ (m1_pre_topc @ X11 @ X12)
% 0.46/0.63          | (m1_subset_1 @ (sk_C @ X11 @ X12) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.63          | (v1_tsep_1 @ X11 @ X12)
% 0.46/0.63          | ~ (l1_pre_topc @ X12))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.63  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf(d5_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.63             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.46/0.63          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.46/0.63          | (v3_pre_topc @ X1 @ X2)
% 0.46/0.63          | ~ (l1_pre_topc @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.46/0.63        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.63  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63        | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.46/0.63        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.46/0.63         | (v3_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.46/0.63         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '16'])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.46/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.46/0.63         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.63         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.46/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X11 : $i, X12 : $i]:
% 0.46/0.63         (~ (m1_pre_topc @ X11 @ X12)
% 0.46/0.63          | ~ (v3_pre_topc @ (sk_C @ X11 @ X12) @ X12)
% 0.46/0.63          | (v1_tsep_1 @ X11 @ X12)
% 0.46/0.63          | ~ (l1_pre_topc @ X12))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.63         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['5'])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.46/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('clc', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      ((((v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63         | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))))
% 0.46/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('clc', [status(thm)], ['19', '27'])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['5'])).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.46/0.63         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('clc', [status(thm)], ['28', '29'])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.46/0.63       ~
% 0.46/0.63       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.63          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.46/0.63       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('split', [status(esa)], ['5'])).
% 0.46/0.63  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['5'])).
% 0.46/0.63  thf('34', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.63  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t1_tsep_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.63           ( m1_subset_1 @
% 0.46/0.63             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      (![X25 : $i, X26 : $i]:
% 0.46/0.63         (~ (m1_pre_topc @ X25 @ X26)
% 0.46/0.63          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.46/0.63          | ~ (l1_pre_topc @ X26))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.63  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf(t114_tmap_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.63           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.46/0.63             ( ![C:$i]:
% 0.46/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.46/0.63                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.46/0.63                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.63         ((v2_struct_0 @ X22)
% 0.46/0.63          | ~ (m1_pre_topc @ X22 @ X23)
% 0.46/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.63          | ((u1_pre_topc @ (k8_tmap_1 @ X23 @ X22)) = (k5_tmap_1 @ X23 @ X24))
% 0.46/0.63          | ((X24) != (u1_struct_0 @ X22))
% 0.46/0.63          | ~ (l1_pre_topc @ X23)
% 0.46/0.63          | ~ (v2_pre_topc @ X23)
% 0.46/0.63          | (v2_struct_0 @ X23))),
% 0.46/0.63      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i]:
% 0.46/0.63         ((v2_struct_0 @ X23)
% 0.46/0.63          | ~ (v2_pre_topc @ X23)
% 0.46/0.63          | ~ (l1_pre_topc @ X23)
% 0.46/0.63          | ((u1_pre_topc @ (k8_tmap_1 @ X23 @ X22))
% 0.46/0.63              = (k5_tmap_1 @ X23 @ (u1_struct_0 @ X22)))
% 0.46/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.46/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.63          | ~ (m1_pre_topc @ X22 @ X23)
% 0.46/0.63          | (v2_struct_0 @ X22))),
% 0.46/0.63      inference('simplify', [status(thm)], ['40'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_B)
% 0.46/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.63        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | (v2_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['39', '41'])).
% 0.46/0.63  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_B)
% 0.46/0.63        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.63        | (v2_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.46/0.63  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('clc', [status(thm)], ['46', '47'])).
% 0.46/0.63  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.63          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['51'])).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.63         (~ (m1_pre_topc @ X11 @ X12)
% 0.46/0.63          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.46/0.63          | ((X13) != (u1_struct_0 @ X11))
% 0.46/0.63          | (v3_pre_topc @ X13 @ X12)
% 0.46/0.63          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.63          | ~ (l1_pre_topc @ X12))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      (![X11 : $i, X12 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X12)
% 0.46/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.46/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.63          | (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.46/0.63          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.46/0.63          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.46/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.46/0.63  thf('56', plain,
% 0.46/0.63      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.63        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['53', '55'])).
% 0.46/0.63  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('59', plain,
% 0.46/0.63      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.63        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.46/0.63  thf('60', plain,
% 0.46/0.63      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.46/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['52', '59'])).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      (![X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.46/0.63          | ~ (v3_pre_topc @ X1 @ X2)
% 0.46/0.63          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.46/0.63          | ~ (l1_pre_topc @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.46/0.63  thf('63', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.46/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.63  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.46/0.63        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      (((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.46/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['60', '65'])).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf(t103_tmap_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.46/0.63             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (![X16 : $i, X17 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.63          | ~ (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.46/0.63          | ((u1_pre_topc @ X17) = (k5_tmap_1 @ X17 @ X16))
% 0.46/0.63          | ~ (l1_pre_topc @ X17)
% 0.46/0.63          | ~ (v2_pre_topc @ X17)
% 0.46/0.63          | (v2_struct_0 @ X17))),
% 0.46/0.63      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.63        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.63        | ~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.46/0.63  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('74', plain,
% 0.46/0.63      ((~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.46/0.63        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('clc', [status(thm)], ['72', '73'])).
% 0.46/0.63  thf('75', plain,
% 0.46/0.63      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.46/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['66', '74'])).
% 0.46/0.63  thf('76', plain,
% 0.46/0.63      ((((u1_pre_topc @ sk_A) = (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.46/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['50', '75'])).
% 0.46/0.63  thf('77', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('78', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i]:
% 0.46/0.63         ((v2_struct_0 @ X22)
% 0.46/0.63          | ~ (m1_pre_topc @ X22 @ X23)
% 0.46/0.63          | ((u1_struct_0 @ (k8_tmap_1 @ X23 @ X22)) = (u1_struct_0 @ X23))
% 0.46/0.63          | ~ (l1_pre_topc @ X23)
% 0.46/0.63          | ~ (v2_pre_topc @ X23)
% 0.46/0.63          | (v2_struct_0 @ X23))),
% 0.46/0.63      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.46/0.63  thf('79', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.46/0.63        | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.63  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('82', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.46/0.63        | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.46/0.63  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('84', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_B)
% 0.46/0.63        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('clc', [status(thm)], ['82', '83'])).
% 0.46/0.63  thf('85', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('86', plain,
% 0.46/0.63      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['84', '85'])).
% 0.46/0.63  thf(abstractness_v1_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ( v1_pre_topc @ A ) =>
% 0.46/0.63         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.46/0.63  thf('87', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_pre_topc @ X0)
% 0.46/0.63          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.63          | ~ (l1_pre_topc @ X0))),
% 0.46/0.63      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.46/0.63  thf('88', plain,
% 0.46/0.63      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.46/0.63          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.46/0.63        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['86', '87'])).
% 0.46/0.63  thf('89', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_k8_tmap_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.63         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.63       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.46/0.63         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.46/0.63         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.46/0.63  thf('90', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X14)
% 0.46/0.63          | ~ (v2_pre_topc @ X14)
% 0.46/0.63          | (v2_struct_0 @ X14)
% 0.46/0.63          | ~ (m1_pre_topc @ X15 @ X14)
% 0.46/0.63          | (l1_pre_topc @ (k8_tmap_1 @ X14 @ X15)))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.46/0.63  thf('91', plain,
% 0.46/0.63      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63        | (v2_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['89', '90'])).
% 0.46/0.63  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('94', plain,
% 0.46/0.63      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.46/0.63  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('96', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('clc', [status(thm)], ['94', '95'])).
% 0.46/0.63  thf('97', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('98', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X14)
% 0.46/0.63          | ~ (v2_pre_topc @ X14)
% 0.46/0.63          | (v2_struct_0 @ X14)
% 0.46/0.63          | ~ (m1_pre_topc @ X15 @ X14)
% 0.46/0.63          | (v1_pre_topc @ (k8_tmap_1 @ X14 @ X15)))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.46/0.63  thf('99', plain,
% 0.46/0.63      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63        | (v2_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['97', '98'])).
% 0.46/0.63  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('102', plain,
% 0.46/0.63      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.46/0.63  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('104', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('clc', [status(thm)], ['102', '103'])).
% 0.46/0.63  thf('105', plain,
% 0.46/0.63      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.46/0.63         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['88', '96', '104'])).
% 0.46/0.63  thf('106', plain,
% 0.46/0.63      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.46/0.63          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.63         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['76', '105'])).
% 0.46/0.63  thf('107', plain,
% 0.46/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.63          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.63         <= (~
% 0.46/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.63                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.46/0.63      inference('split', [status(esa)], ['5'])).
% 0.46/0.63  thf('108', plain,
% 0.46/0.63      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.63         <= (~
% 0.46/0.63             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.63                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.46/0.63             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['106', '107'])).
% 0.46/0.63  thf('109', plain,
% 0.46/0.63      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.63          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.46/0.63       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('simplify', [status(thm)], ['108'])).
% 0.46/0.63  thf('110', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['31', '34', '109'])).
% 0.46/0.63  thf('111', plain,
% 0.46/0.63      (~ (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['30', '110'])).
% 0.46/0.63  thf('112', plain,
% 0.46/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('113', plain,
% 0.46/0.63      (![X16 : $i, X17 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.63          | ((u1_pre_topc @ X17) != (k5_tmap_1 @ X17 @ X16))
% 0.46/0.63          | (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.46/0.63          | ~ (l1_pre_topc @ X17)
% 0.46/0.63          | ~ (v2_pre_topc @ X17)
% 0.46/0.63          | (v2_struct_0 @ X17))),
% 0.46/0.63      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.46/0.63  thf('114', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.46/0.63        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['112', '113'])).
% 0.46/0.63  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('117', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.46/0.63        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.46/0.63  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('119', plain,
% 0.46/0.63      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.46/0.63      inference('clc', [status(thm)], ['117', '118'])).
% 0.46/0.63  thf('120', plain,
% 0.46/0.63      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.63         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.63  thf('121', plain,
% 0.46/0.63      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.63        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['119', '120'])).
% 0.46/0.63  thf('122', plain,
% 0.46/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf(t35_connsp_2, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.46/0.63  thf('123', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.63          | (m2_connsp_2 @ (k2_struct_0 @ X10) @ X10 @ X9)
% 0.46/0.63          | ~ (l1_pre_topc @ X10)
% 0.46/0.63          | ~ (v2_pre_topc @ X10)
% 0.46/0.63          | (v2_struct_0 @ X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [t35_connsp_2])).
% 0.46/0.63  thf('124', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['122', '123'])).
% 0.46/0.63  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('127', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_A)
% 0.46/0.63        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.46/0.63  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('129', plain,
% 0.46/0.63      ((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('clc', [status(thm)], ['127', '128'])).
% 0.46/0.63  thf('130', plain,
% 0.46/0.63      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf(dt_m2_connsp_2, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63       ( ![C:$i]:
% 0.46/0.63         ( ( m2_connsp_2 @ C @ A @ B ) =>
% 0.46/0.63           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('131', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X6)
% 0.46/0.63          | ~ (v2_pre_topc @ X6)
% 0.46/0.63          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.46/0.63          | (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.46/0.63          | ~ (m2_connsp_2 @ X8 @ X6 @ X7))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_m2_connsp_2])).
% 0.46/0.63  thf('132', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m2_connsp_2 @ X0 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.63          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63          | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['130', '131'])).
% 0.46/0.63  thf('133', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('135', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m2_connsp_2 @ X0 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.64          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.46/0.64  thf('136', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['129', '135'])).
% 0.46/0.64  thf(t106_tmap_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64           ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.64             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.46/0.64               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.64  thf('137', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.64          | ~ (v3_pre_topc @ X20 @ X21)
% 0.46/0.64          | ((g1_pre_topc @ (u1_struct_0 @ X21) @ (u1_pre_topc @ X21))
% 0.46/0.64              = (k6_tmap_1 @ X21 @ X20))
% 0.46/0.64          | ~ (l1_pre_topc @ X21)
% 0.46/0.64          | ~ (v2_pre_topc @ X21)
% 0.46/0.64          | (v2_struct_0 @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t106_tmap_1])).
% 0.46/0.64  thf('138', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64            = (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.64        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['136', '137'])).
% 0.46/0.64  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t43_tops_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.46/0.64  thf('141', plain,
% 0.46/0.64      (![X5 : $i]:
% 0.46/0.64         (((k1_tops_1 @ X5 @ (k2_struct_0 @ X5)) = (k2_struct_0 @ X5))
% 0.46/0.64          | ~ (l1_pre_topc @ X5)
% 0.46/0.64          | ~ (v2_pre_topc @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.46/0.64  thf('142', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['129', '135'])).
% 0.46/0.64  thf(fc9_tops_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.64       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.46/0.64  thf('143', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X3)
% 0.46/0.64          | ~ (v2_pre_topc @ X3)
% 0.46/0.64          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.46/0.64          | (v3_pre_topc @ (k1_tops_1 @ X3 @ X4) @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.46/0.64  thf('144', plain,
% 0.46/0.64      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) @ sk_A)
% 0.46/0.64        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['142', '143'])).
% 0.46/0.64  thf('145', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('147', plain,
% 0.46/0.64      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.46/0.64  thf('148', plain,
% 0.46/0.64      (((v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.46/0.64        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['141', '147'])).
% 0.46/0.64  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('151', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.46/0.64  thf('152', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64            = (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['138', '139', '140', '151'])).
% 0.46/0.64  thf('153', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('154', plain,
% 0.46/0.64      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64         = (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('clc', [status(thm)], ['152', '153'])).
% 0.46/0.64  thf('155', plain,
% 0.46/0.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.64         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.46/0.64      inference('split', [status(esa)], ['51'])).
% 0.46/0.64  thf('156', plain,
% 0.46/0.64      ((((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.64         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['154', '155'])).
% 0.46/0.64  thf('157', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['129', '135'])).
% 0.46/0.64  thf(t104_tmap_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.46/0.64             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.64  thf('158', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.46/0.64          | ((u1_pre_topc @ (k6_tmap_1 @ X19 @ X18)) = (k5_tmap_1 @ X19 @ X18))
% 0.46/0.64          | ~ (l1_pre_topc @ X19)
% 0.46/0.64          | ~ (v2_pre_topc @ X19)
% 0.46/0.64          | (v2_struct_0 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.46/0.64  thf('159', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.64            = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['157', '158'])).
% 0.46/0.64  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('162', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.64            = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.46/0.64  thf('163', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('164', plain,
% 0.46/0.64      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.64         = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('clc', [status(thm)], ['162', '163'])).
% 0.46/0.64  thf('165', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['129', '135'])).
% 0.46/0.64  thf('166', plain,
% 0.46/0.64      (![X16 : $i, X17 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.64          | ~ (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.46/0.64          | ((u1_pre_topc @ X17) = (k5_tmap_1 @ X17 @ X16))
% 0.46/0.64          | ~ (l1_pre_topc @ X17)
% 0.46/0.64          | ~ (v2_pre_topc @ X17)
% 0.46/0.64          | (v2_struct_0 @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.46/0.64  thf('167', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.64        | ~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['165', '166'])).
% 0.46/0.64  thf('168', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('170', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['129', '135'])).
% 0.46/0.64  thf('171', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.46/0.64          | ~ (v3_pre_topc @ X1 @ X2)
% 0.46/0.64          | (r2_hidden @ X1 @ (u1_pre_topc @ X2))
% 0.46/0.64          | ~ (l1_pre_topc @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.46/0.64  thf('172', plain,
% 0.46/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.64        | (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['170', '171'])).
% 0.46/0.64  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('174', plain,
% 0.46/0.64      (((r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['172', '173'])).
% 0.46/0.64  thf('175', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.46/0.64  thf('176', plain,
% 0.46/0.64      ((r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['174', '175'])).
% 0.46/0.64  thf('177', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['167', '168', '169', '176'])).
% 0.46/0.64  thf('178', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('179', plain,
% 0.46/0.64      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('clc', [status(thm)], ['177', '178'])).
% 0.46/0.64  thf('180', plain,
% 0.46/0.64      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.64         = (u1_pre_topc @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['164', '179'])).
% 0.46/0.64  thf('181', plain,
% 0.46/0.64      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A)))
% 0.46/0.64         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['156', '180'])).
% 0.46/0.64  thf('182', plain,
% 0.46/0.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.46/0.64       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.64      inference('split', [status(esa)], ['51'])).
% 0.46/0.64  thf('183', plain,
% 0.46/0.64      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.64          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['31', '34', '109', '182'])).
% 0.46/0.64  thf('184', plain,
% 0.46/0.64      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['181', '183'])).
% 0.46/0.64  thf('185', plain,
% 0.46/0.64      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.46/0.64        | (r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['121', '184'])).
% 0.46/0.64  thf('186', plain,
% 0.46/0.64      ((r2_hidden @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.46/0.64      inference('simplify', [status(thm)], ['185'])).
% 0.46/0.64  thf('187', plain, ($false), inference('demod', [status(thm)], ['111', '186'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
