%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1EZTCqj3Ww

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 479 expanded)
%              Number of leaves         :   20 ( 141 expanded)
%              Depth                    :   20
%              Number of atoms          :  823 (9492 expanded)
%              Number of equality atoms :   56 ( 717 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(t114_tmap_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                      = ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X7 @ X6 ) )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k8_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( C
                        = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( X2
       != ( k8_tmap_1 @ X1 @ X0 ) )
      | ( X3
       != ( u1_struct_0 @ X0 ) )
      | ( X2
        = ( k6_tmap_1 @ X1 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( ( k8_tmap_1 @ X1 @ X0 )
        = ( k6_tmap_1 @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('22',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('31',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('42',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['2','57'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X7 @ X6 ) )
        = ( k5_tmap_1 @ X7 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
      = ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
      = ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( sk_C
      = ( u1_struct_0 @ sk_B ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['52'])).

thf('65',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','47'])).

thf('66',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ sk_C ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) )
   <= ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) )
   <= ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
       != ( k5_tmap_1 @ sk_A @ sk_C ) )
      & ( sk_C
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['67'])).

thf('71',plain,(
    ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
 != ( k5_tmap_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['55','70'])).

thf('72',plain,
    ( ( sk_C
      = ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('73',plain,
    ( sk_C
    = ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['55','72'])).

thf('74',plain,(
    ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
 != ( k5_tmap_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['69','71','73'])).

thf('75',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['63','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1EZTCqj3Ww
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:18:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 62 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.21/0.49  thf(t114_tmap_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.49             ( ![C:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.21/0.49                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49              ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.49                ( ![C:$i]:
% 0.21/0.49                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49                    ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                      ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.21/0.49                        ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t114_tmap_1])).
% 0.21/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))
% 0.21/0.49        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.49      inference('split', [status(esa)], ['1'])).
% 0.21/0.49  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t1_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( m1_subset_1 @
% 0.21/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.49          | (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.49          | ~ (l1_pre_topc @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t104_tmap_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.49             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.49          | ((u1_struct_0 @ (k6_tmap_1 @ X7 @ X6)) = (u1_struct_0 @ X7))
% 0.21/0.49          | ~ (l1_pre_topc @ X7)
% 0.21/0.49          | ~ (v2_pre_topc @ X7)
% 0.21/0.49          | (v2_struct_0 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.21/0.49            = (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(d11_tmap_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.21/0.49                 ( l1_pre_topc @ C ) ) =>
% 0.21/0.49               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.21/0.49                 ( ![D:$i]:
% 0.21/0.49                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.49          | ((X2) != (k8_tmap_1 @ X1 @ X0))
% 0.21/0.49          | ((X3) != (u1_struct_0 @ X0))
% 0.21/0.49          | ((X2) = (k6_tmap_1 @ X1 @ X3))
% 0.21/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (l1_pre_topc @ X2)
% 0.21/0.49          | ~ (v2_pre_topc @ X2)
% 0.21/0.49          | ~ (v1_pre_topc @ X2)
% 0.21/0.49          | ~ (l1_pre_topc @ X1)
% 0.21/0.49          | ~ (v2_pre_topc @ X1)
% 0.21/0.49          | (v2_struct_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X1)
% 0.21/0.49          | ~ (v2_pre_topc @ X1)
% 0.21/0.49          | ~ (l1_pre_topc @ X1)
% 0.21/0.49          | ~ (v1_pre_topc @ (k8_tmap_1 @ X1 @ X0))
% 0.21/0.49          | ~ (v2_pre_topc @ (k8_tmap_1 @ X1 @ X0))
% 0.21/0.49          | ~ (l1_pre_topc @ (k8_tmap_1 @ X1 @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ((k8_tmap_1 @ X1 @ X0) = (k6_tmap_1 @ X1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.49        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.21/0.49            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.21/0.49        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.49  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.21/0.49        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.21/0.49  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k8_tmap_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.49         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.49         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X4)
% 0.21/0.49          | ~ (v2_pre_topc @ X4)
% 0.21/0.49          | (v2_struct_0 @ X4)
% 0.21/0.49          | ~ (m1_pre_topc @ X5 @ X4)
% 0.21/0.49          | (l1_pre_topc @ (k8_tmap_1 @ X4 @ X5)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.49  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.21/0.49        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '27'])).
% 0.21/0.49  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X4)
% 0.21/0.49          | ~ (v2_pre_topc @ X4)
% 0.21/0.49          | (v2_struct_0 @ X4)
% 0.21/0.49          | ~ (m1_pre_topc @ X5 @ X4)
% 0.21/0.49          | (v2_pre_topc @ (k8_tmap_1 @ X4 @ X5)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.49  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.21/0.49        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['28', '36'])).
% 0.21/0.49  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.21/0.49            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X4)
% 0.21/0.49          | ~ (v2_pre_topc @ X4)
% 0.21/0.49          | (v2_struct_0 @ X4)
% 0.21/0.49          | ~ (m1_pre_topc @ X5 @ X4)
% 0.21/0.49          | (v1_pre_topc @ (k8_tmap_1 @ X4 @ X5)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.49  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10', '11', '48'])).
% 0.21/0.49  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))
% 0.21/0.49        | ((sk_C) = (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['52'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.49       ~ (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['1'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['2', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.49          | ((u1_pre_topc @ (k6_tmap_1 @ X7 @ X6)) = (k5_tmap_1 @ X7 @ X6))
% 0.21/0.49          | ~ (l1_pre_topc @ X7)
% 0.21/0.49          | ~ (v2_pre_topc @ X7)
% 0.21/0.49          | (v2_struct_0 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.21/0.49            = (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.49  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.21/0.49            = (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      ((((sk_C) = (u1_struct_0 @ sk_B))) <= ((((sk_C) = (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['52'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '47'])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ sk_C)))
% 0.21/0.49         <= ((((sk_C) = (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['64', '65'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))
% 0.21/0.49        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49            != (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) != (k5_tmap_1 @ sk_A @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49                = (k5_tmap_1 @ sk_A @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['67'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C)) != (k5_tmap_1 @ sk_A @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.49                = (k5_tmap_1 @ sk_A @ sk_C))) & 
% 0.21/0.49             (((sk_C) = (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['66', '68'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (~
% 0.21/0.49       (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_C))) | 
% 0.21/0.49       ~ (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['67'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (~
% 0.21/0.49       (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['55', '70'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      ((((sk_C) = (u1_struct_0 @ sk_B))) | 
% 0.21/0.49       ~ (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['52'])).
% 0.21/0.49  thf('73', plain, ((((sk_C) = (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['55', '72'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C)) != (k5_tmap_1 @ sk_A @ sk_C))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['69', '71', '73'])).
% 0.21/0.49  thf('75', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['63', '74'])).
% 0.21/0.49  thf('76', plain, ($false), inference('demod', [status(thm)], ['0', '75'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
