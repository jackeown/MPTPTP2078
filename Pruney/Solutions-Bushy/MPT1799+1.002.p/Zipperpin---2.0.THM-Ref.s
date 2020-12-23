%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1799+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f80sCpAEuV

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:16 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 894 expanded)
%              Number of leaves         :   22 ( 270 expanded)
%              Depth                    :   16
%              Number of atoms          :  931 (16732 expanded)
%              Number of equality atoms :   31 ( 557 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(t115_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) )
             => ( ( ( u1_struct_0 @ C )
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) )
                  & ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) )
               => ( ( ( u1_struct_0 @ C )
                    = ( u1_struct_0 @ B ) )
                 => ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) )
                    & ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
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

thf('3',plain,(
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
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
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
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
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
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['13'])).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('22',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
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
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('30',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
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
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('38',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
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
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect+',[status(thm)],['14','27','35','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf(t105_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) )
             => ( ( C = B )
               => ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X8 != X6 )
      | ( v3_pre_topc @ X8 @ ( k6_tmap_1 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X7 @ X6 ) ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t105_tmap_1])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X7 @ X6 ) ) ) )
      | ( v3_pre_topc @ X6 @ ( k6_tmap_1 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('54',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('55',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('58',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','56','57','58','59','60'])).

thf('62',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ~ ( v3_pre_topc @ X11 @ X10 )
      | ( v1_tsep_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_tsep_1 @ X9 @ X10 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X9 ) @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('68',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('69',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('70',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67','70'])).

thf('72',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['72'])).

thf('76',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['72'])).

thf('78',plain,(
    ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['73','78'])).

thf('80',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['71','79'])).

thf('81',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['61','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81'])).


%------------------------------------------------------------------------------
