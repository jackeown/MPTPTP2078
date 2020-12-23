%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LmCZX9NCfY

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 572 expanded)
%              Number of leaves         :   21 ( 170 expanded)
%              Depth                    :   18
%              Number of atoms          :  903 (11346 expanded)
%              Number of equality atoms :   64 ( 856 expanded)
%              Maximal formula depth    :   18 (   5 average)

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

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( sk_D @ X2 @ X0 @ X1 )
        = ( u1_struct_0 @ X0 ) )
      | ( X2
        = ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( X2
       != ( k6_tmap_1 @ X1 @ ( sk_D @ X2 @ X0 @ X1 ) ) )
      | ( X2
        = ( k8_tmap_1 @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('30',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('38',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('46',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect+',[status(thm)],['27','35','43','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','54'])).

thf('56',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['2','61'])).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X7 @ X6 ) )
        = ( k5_tmap_1 @ X7 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
      = ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
      = ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) )
   <= ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( sk_C
      = ( u1_struct_0 @ sk_B ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['56'])).

thf('71',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('72',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_C )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_C
      = ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['56'])).

thf('74',plain,
    ( sk_C
    = ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['59','73'])).

thf('75',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_C )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) )
   <= ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','75'])).

thf('77',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['68'])).

thf('78',plain,(
    ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
 != ( k5_tmap_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['59','77'])).

thf('79',plain,(
    ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
 != ( k5_tmap_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['67','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LmCZX9NCfY
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 129 iterations in 0.093s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.20/0.55  thf(t114_tmap_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.55           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.55             ( ![C:$i]:
% 0.20/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.20/0.55                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55            ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.55              ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.55                ( ![C:$i]:
% 0.20/0.55                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                    ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                      ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.20/0.55                        ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t114_tmap_1])).
% 0.20/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))
% 0.20/0.55        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.55         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.55      inference('split', [status(esa)], ['1'])).
% 0.20/0.55  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t1_tsep_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( m1_subset_1 @
% 0.20/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.55          | (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.55          | ~ (l1_pre_topc @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf(t104_tmap_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.55             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.55          | ((u1_struct_0 @ (k6_tmap_1 @ X7 @ X6)) = (u1_struct_0 @ X7))
% 0.20/0.55          | ~ (l1_pre_topc @ X7)
% 0.20/0.55          | ~ (v2_pre_topc @ X7)
% 0.20/0.55          | (v2_struct_0 @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55            = (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55            = (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.55  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55         = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d11_tmap_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.20/0.55                 ( l1_pre_topc @ C ) ) =>
% 0.20/0.55               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.20/0.55                 ( ![D:$i]:
% 0.20/0.55                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.55          | ((sk_D @ X2 @ X0 @ X1) = (u1_struct_0 @ X0))
% 0.20/0.55          | ((X2) = (k8_tmap_1 @ X1 @ X0))
% 0.20/0.55          | ~ (l1_pre_topc @ X2)
% 0.20/0.55          | ~ (v2_pre_topc @ X2)
% 0.20/0.55          | ~ (v1_pre_topc @ X2)
% 0.20/0.55          | ~ (l1_pre_topc @ X1)
% 0.20/0.55          | ~ (v2_pre_topc @ X1)
% 0.20/0.55          | (v2_struct_0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55          | ~ (v1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.55          | ((sk_D @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (v1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.55          | ((sk_D @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.55          | ((X2) != (k6_tmap_1 @ X1 @ (sk_D @ X2 @ X0 @ X1)))
% 0.20/0.55          | ((X2) = (k8_tmap_1 @ X1 @ X0))
% 0.20/0.55          | ~ (l1_pre_topc @ X2)
% 0.20/0.55          | ~ (v2_pre_topc @ X2)
% 0.20/0.55          | ~ (v1_pre_topc @ X2)
% 0.20/0.55          | ~ (l1_pre_topc @ X1)
% 0.20/0.55          | ~ (v2_pre_topc @ X1)
% 0.20/0.55          | (v2_struct_0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((X0) != (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (v1_pre_topc @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55          | ~ (v1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.55          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((X0) != (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (v1_pre_topc @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (v1_pre_topc @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.20/0.55            = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf(dt_k6_tmap_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55         ( l1_pre_topc @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.20/0.55         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.20/0.55         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X4)
% 0.20/0.55          | ~ (v2_pre_topc @ X4)
% 0.20/0.55          | (v2_struct_0 @ X4)
% 0.20/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.55          | (l1_pre_topc @ (k6_tmap_1 @ X4 @ X5)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.55  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('35', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X4)
% 0.20/0.55          | ~ (v2_pre_topc @ X4)
% 0.20/0.55          | (v2_struct_0 @ X4)
% 0.20/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.55          | (v2_pre_topc @ (k6_tmap_1 @ X4 @ X5)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.55  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.55  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('43', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X4)
% 0.20/0.55          | ~ (v2_pre_topc @ X4)
% 0.20/0.55          | (v2_struct_0 @ X4)
% 0.20/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.55          | (v1_pre_topc @ (k6_tmap_1 @ X4 @ X5)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.55  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.55  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('51', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.20/0.55            = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('simplify_reflect+', [status(thm)], ['27', '35', '43', '51'])).
% 0.20/0.55  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['14', '54'])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))
% 0.20/0.55        | ((sk_C) = (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['56'])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['55', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.55       ~ (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['1'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['59', '60'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['2', '61'])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.55          | ((u1_pre_topc @ (k6_tmap_1 @ X7 @ X6)) = (k5_tmap_1 @ X7 @ X6))
% 0.20/0.55          | ~ (l1_pre_topc @ X7)
% 0.20/0.55          | ~ (v2_pre_topc @ X7)
% 0.20/0.55          | (v2_struct_0 @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.20/0.55            = (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.55  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C))
% 0.20/0.55            = (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))
% 0.20/0.55        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.55            != (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      ((((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) != (k5_tmap_1 @ sk_A @ sk_C)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.55                = (k5_tmap_1 @ sk_A @ sk_C))))),
% 0.20/0.55      inference('split', [status(esa)], ['68'])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      ((((sk_C) = (u1_struct_0 @ sk_B))) <= ((((sk_C) = (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['56'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      ((((k6_tmap_1 @ sk_A @ sk_C) = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= ((((sk_C) = (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['70', '71'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      ((((sk_C) = (u1_struct_0 @ sk_B))) | 
% 0.20/0.55       ~ (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['56'])).
% 0.20/0.55  thf('74', plain, ((((sk_C) = (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['59', '73'])).
% 0.20/0.55  thf('75', plain, (((k6_tmap_1 @ sk_A @ sk_C) = (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C)) != (k5_tmap_1 @ sk_A @ sk_C)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.55                = (k5_tmap_1 @ sk_A @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['69', '75'])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      (~
% 0.20/0.55       (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_C))) | 
% 0.20/0.55       ~ (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['68'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (~
% 0.20/0.55       (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_C)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['59', '77'])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_C)) != (k5_tmap_1 @ sk_A @ sk_C))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 0.20/0.55  thf('80', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['67', '79'])).
% 0.20/0.55  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
