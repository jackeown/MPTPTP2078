%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1800+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ytEEEcVl6Y

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:16 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 362 expanded)
%              Number of leaves         :   24 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          : 1175 (5830 expanded)
%              Number of equality atoms :   58 ( 232 expanded)
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

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

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

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
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

thf('6',plain,(
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

thf('7',plain,(
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
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
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

thf('12',plain,(
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
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('24',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('32',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('40',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect+',[status(thm)],['17','29','37','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['49'])).

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

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
       != ( k6_tmap_1 @ X10 @ X9 ) )
      | ( v3_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('52',plain,
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
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('58',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( ( sk_C @ X4 @ X5 )
        = ( u1_struct_0 @ X4 ) )
      | ( v1_tsep_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( v3_pre_topc @ ( sk_C @ X4 @ X5 ) @ X5 )
      | ( v1_tsep_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('70',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','75'])).

thf('77',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['49'])).

thf('78',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('79',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('80',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ~ ( v1_tsep_1 @ X4 @ X5 )
      | ( X6
       != ( u1_struct_0 @ X4 ) )
      | ( v3_pre_topc @ X6 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('81',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X4 ) @ X5 )
      | ~ ( v1_tsep_1 @ X4 @ X5 )
      | ~ ( m1_pre_topc @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('88',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
        = ( k6_tmap_1 @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','95'])).

thf('97',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','4','76','77','99'])).


%------------------------------------------------------------------------------
