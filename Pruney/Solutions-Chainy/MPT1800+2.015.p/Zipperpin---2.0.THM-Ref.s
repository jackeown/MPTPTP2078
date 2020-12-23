%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cifW8nJMYj

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 804 expanded)
%              Number of leaves         :   27 ( 236 expanded)
%              Depth                    :   18
%              Number of atoms          : 1484 (12773 expanded)
%              Number of equality atoms :   72 ( 504 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( sk_C @ X1 @ X2 )
        = ( u1_struct_0 @ X1 ) )
      | ( v1_tsep_1 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v3_pre_topc @ ( sk_C @ X1 @ X2 ) @ X2 )
      | ( v1_tsep_1 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('9',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('14',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X9 @ X8 ) )
        = ( k5_tmap_1 @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X13 @ X12 ) )
        = ( k5_tmap_1 @ X13 @ X14 ) )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X13 @ X12 ) )
        = ( k5_tmap_1 @ X13 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','38'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('41',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X9 @ X8 ) )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X12 ) )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('61',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('64',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('72',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','69','77'])).

thf('79',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('81',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('88',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('89',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','49','78','86','94'])).

thf('96',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['96'])).

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

thf('98',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) )
       != ( k6_tmap_1 @ X11 @ X10 ) )
      | ( v3_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','102'])).

thf('104',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('105',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('108',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('110',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','49','78','86','94'])).

thf('112',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['96'])).

thf('113',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('114',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_tsep_1 @ X1 @ X2 )
      | ( X3
       != ( u1_struct_0 @ X1 ) )
      | ( v3_pre_topc @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('115',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X1 ) @ X2 )
      | ~ ( v1_tsep_1 @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['113','115'])).

thf('117',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','119'])).

thf('121',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('122',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) )
        = ( k6_tmap_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','128'])).

thf('130',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('131',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','131'])).

thf('133',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['96'])).

thf('135',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['107','110','133','134'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['106','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( $false
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','138'])).

thf('140',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['107','110','133'])).

thf('141',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['139','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cifW8nJMYj
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 136 iterations in 0.044s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.20/0.48  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.20/0.48  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(t116_tmap_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.48           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.48             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.48               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48            ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.48              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.48                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.48                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.20/0.48  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d1_tsep_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.48          | ((sk_C @ X1 @ X2) = (u1_struct_0 @ X1))
% 0.20/0.48          | (v1_tsep_1 @ X1 @ X2)
% 0.20/0.48          | ~ (l1_pre_topc @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.48        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.48        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.20/0.48         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.48          | ~ (v3_pre_topc @ (sk_C @ X1 @ X2) @ X2)
% 0.20/0.48          | (v1_tsep_1 @ X1 @ X2)
% 0.20/0.48          | ~ (l1_pre_topc @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.48         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.48         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.48         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t1_tsep_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( m1_subset_1 @
% 0.20/0.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.48          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | ~ (l1_pre_topc @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf(t104_tmap_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.48             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ((u1_pre_topc @ (k6_tmap_1 @ X9 @ X8)) = (k5_tmap_1 @ X9 @ X8))
% 0.20/0.48          | ~ (l1_pre_topc @ X9)
% 0.20/0.48          | ~ (v2_pre_topc @ X9)
% 0.20/0.48          | (v2_struct_0 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.48  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf(t114_tmap_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.48           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.20/0.48                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X12)
% 0.20/0.48          | ~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.48          | ((u1_pre_topc @ (k8_tmap_1 @ X13 @ X12)) = (k5_tmap_1 @ X13 @ X14))
% 0.20/0.48          | ((X14) != (u1_struct_0 @ X12))
% 0.20/0.48          | ~ (l1_pre_topc @ X13)
% 0.20/0.48          | ~ (v2_pre_topc @ X13)
% 0.20/0.48          | (v2_struct_0 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X13)
% 0.20/0.48          | ~ (v2_pre_topc @ X13)
% 0.20/0.48          | ~ (l1_pre_topc @ X13)
% 0.20/0.48          | ((u1_pre_topc @ (k8_tmap_1 @ X13 @ X12))
% 0.20/0.48              = (k5_tmap_1 @ X13 @ (u1_struct_0 @ X12)))
% 0.20/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.48          | ~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.48          | (v2_struct_0 @ X12))),
% 0.20/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_B)
% 0.20/0.48        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.48        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.48  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_B)
% 0.20/0.48        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.20/0.48  thf('35', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('clc', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48         = (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '38'])).
% 0.20/0.48  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ( v1_pre_topc @ A ) =>
% 0.20/0.48         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_pre_topc @ X0)
% 0.20/0.48          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.20/0.48          = (g1_pre_topc @ 
% 0.20/0.48             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.20/0.48             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.20/0.48        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ((u1_struct_0 @ (k6_tmap_1 @ X9 @ X8)) = (u1_struct_0 @ X9))
% 0.20/0.48          | ~ (l1_pre_topc @ X9)
% 0.20/0.48          | ~ (v2_pre_topc @ X9)
% 0.20/0.48          | (v2_struct_0 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48            = (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48            = (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.48  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48         = (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X12)
% 0.20/0.48          | ~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.48          | ((u1_struct_0 @ (k8_tmap_1 @ X13 @ X12)) = (u1_struct_0 @ X13))
% 0.20/0.48          | ~ (l1_pre_topc @ X13)
% 0.20/0.48          | ~ (v2_pre_topc @ X13)
% 0.20/0.48          | (v2_struct_0 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.48  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_B)
% 0.20/0.48        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_pre_topc @ X0)
% 0.20/0.48          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.48          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.20/0.48        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.48  thf('62', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k8_tmap_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.48       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.48         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.48         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X6)
% 0.20/0.48          | ~ (v2_pre_topc @ X6)
% 0.20/0.48          | (v2_struct_0 @ X6)
% 0.20/0.48          | ~ (m1_pre_topc @ X7 @ X6)
% 0.20/0.48          | (l1_pre_topc @ (k8_tmap_1 @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.20/0.48  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('69', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['67', '68'])).
% 0.20/0.48  thf('70', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('71', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X6)
% 0.20/0.48          | ~ (v2_pre_topc @ X6)
% 0.20/0.48          | (v2_struct_0 @ X6)
% 0.20/0.48          | ~ (m1_pre_topc @ X7 @ X6)
% 0.20/0.48          | (v1_pre_topc @ (k8_tmap_1 @ X6 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.48  thf('72', plain,
% 0.20/0.48      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.48  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('75', plain,
% 0.20/0.48      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.20/0.48  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('77', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['75', '76'])).
% 0.20/0.48  thf('78', plain,
% 0.20/0.48      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.48         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['61', '69', '77'])).
% 0.20/0.48  thf('79', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf(dt_k6_tmap_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48         ( l1_pre_topc @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.20/0.48         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.20/0.48         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X4)
% 0.20/0.48          | ~ (v2_pre_topc @ X4)
% 0.20/0.48          | (v2_struct_0 @ X4)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | (l1_pre_topc @ (k6_tmap_1 @ X4 @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.20/0.48  thf('81', plain,
% 0.20/0.48      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.48  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('84', plain,
% 0.20/0.48      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.20/0.48  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('86', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['84', '85'])).
% 0.20/0.48  thf('87', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('88', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X4)
% 0.20/0.48          | ~ (v2_pre_topc @ X4)
% 0.20/0.48          | (v2_struct_0 @ X4)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | (v1_pre_topc @ (k6_tmap_1 @ X4 @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.20/0.48  thf('89', plain,
% 0.20/0.48      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.48  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('92', plain,
% 0.20/0.48      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.20/0.48  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('94', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.48  thf('95', plain,
% 0.20/0.48      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '49', '78', '86', '94'])).
% 0.20/0.48  thf('96', plain,
% 0.20/0.48      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('97', plain,
% 0.20/0.48      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.48         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['96'])).
% 0.20/0.48  thf(t106_tmap_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.48             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.48               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.48  thf('98', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | ((g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))
% 0.20/0.48              != (k6_tmap_1 @ X11 @ X10))
% 0.20/0.48          | (v3_pre_topc @ X10 @ X11)
% 0.20/0.48          | ~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (v2_pre_topc @ X11)
% 0.20/0.48          | (v2_struct_0 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t106_tmap_1])).
% 0.20/0.48  thf('99', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 0.20/0.48           | (v2_struct_0 @ sk_A)
% 0.20/0.48           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.48           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.48         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.48  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('102', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 0.20/0.48           | (v2_struct_0 @ sk_A)
% 0.20/0.48           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.48           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.48         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.20/0.48  thf('103', plain,
% 0.20/0.48      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.48         | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['95', '102'])).
% 0.20/0.48  thf('104', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('105', plain,
% 0.20/0.48      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.48         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.48         | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.48  thf('106', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A) | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)))
% 0.20/0.48         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['105'])).
% 0.20/0.48  thf('107', plain,
% 0.20/0.48      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.48       ~
% 0.20/0.48       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.48       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('108', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('109', plain,
% 0.20/0.48      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('110', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.48  thf('111', plain,
% 0.20/0.48      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '49', '78', '86', '94'])).
% 0.20/0.48  thf('112', plain,
% 0.20/0.48      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['96'])).
% 0.20/0.48  thf('113', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('114', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X1 @ X2)
% 0.20/0.48          | ~ (v1_tsep_1 @ X1 @ X2)
% 0.20/0.48          | ((X3) != (u1_struct_0 @ X1))
% 0.20/0.48          | (v3_pre_topc @ X3 @ X2)
% 0.20/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.48          | ~ (l1_pre_topc @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.20/0.48  thf('115', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X2)
% 0.20/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X1) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.48          | (v3_pre_topc @ (u1_struct_0 @ X1) @ X2)
% 0.20/0.48          | ~ (v1_tsep_1 @ X1 @ X2)
% 0.20/0.48          | ~ (m1_pre_topc @ X1 @ X2))),
% 0.20/0.48      inference('simplify', [status(thm)], ['114'])).
% 0.20/0.48  thf('116', plain,
% 0.20/0.48      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.48        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['113', '115'])).
% 0.20/0.48  thf('117', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('119', plain,
% 0.20/0.48      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.48        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.20/0.48  thf('120', plain,
% 0.20/0.48      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.48         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['112', '119'])).
% 0.20/0.48  thf('121', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('122', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | ~ (v3_pre_topc @ X10 @ X11)
% 0.20/0.48          | ((g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))
% 0.20/0.48              = (k6_tmap_1 @ X11 @ X10))
% 0.20/0.48          | ~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (v2_pre_topc @ X11)
% 0.20/0.48          | (v2_struct_0 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t106_tmap_1])).
% 0.20/0.48  thf('123', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['121', '122'])).
% 0.20/0.48  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('126', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.20/0.48  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('128', plain,
% 0.20/0.48      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.48        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('clc', [status(thm)], ['126', '127'])).
% 0.20/0.48  thf('129', plain,
% 0.20/0.48      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.20/0.48         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['120', '128'])).
% 0.20/0.48  thf('130', plain,
% 0.20/0.48      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('131', plain,
% 0.20/0.48      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.20/0.48             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['129', '130'])).
% 0.20/0.48  thf('132', plain,
% 0.20/0.48      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.20/0.48             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['111', '131'])).
% 0.20/0.48  thf('133', plain,
% 0.20/0.48      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.48       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['132'])).
% 0.20/0.48  thf('134', plain,
% 0.20/0.48      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.48       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['96'])).
% 0.20/0.48  thf('135', plain,
% 0.20/0.48      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.48          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['107', '110', '133', '134'])).
% 0.20/0.48  thf('136', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A) | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['106', '135'])).
% 0.20/0.48  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('138', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['136', '137'])).
% 0.20/0.48  thf('139', plain, (($false) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '138'])).
% 0.20/0.48  thf('140', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['107', '110', '133'])).
% 0.20/0.48  thf('141', plain, ($false),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['139', '140'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
