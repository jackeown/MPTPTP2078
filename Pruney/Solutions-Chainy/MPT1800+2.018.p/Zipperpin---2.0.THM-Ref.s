%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.atdDpx6DTM

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 314 expanded)
%              Number of leaves         :   22 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          : 1067 (5039 expanded)
%              Number of equality atoms :   47 ( 190 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('10',plain,(
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

thf('11',plain,(
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
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('16',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('24',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','21','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('37',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('44',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

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

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) )
       != ( k6_tmap_1 @ X7 @ X6 ) )
      | ( v3_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('47',plain,
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
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('53',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('58',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( X10
       != ( u1_struct_0 @ X8 ) )
      | ~ ( v3_pre_topc @ X10 @ X9 )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('59',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('69',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('70',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( X10
       != ( u1_struct_0 @ X8 ) )
      | ~ ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( v1_tsep_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('80',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) )
        = ( k6_tmap_1 @ X7 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','4','67','68','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.atdDpx6DTM
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 51 iterations in 0.032s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.20/0.49  thf(t116_tmap_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.49             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.49               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.49                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.49                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.49        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.49       ~
% 0.20/0.49       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.49       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('4', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t1_tsep_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.49           ( m1_subset_1 @
% 0.20/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.49          | (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.49          | ~ (l1_pre_topc @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf(d11_tmap_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.20/0.49                 ( l1_pre_topc @ C ) ) =>
% 0.20/0.49               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.20/0.49                 ( ![D:$i]:
% 0.20/0.49                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.49                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.49          | ((X2) != (k8_tmap_1 @ X1 @ X0))
% 0.20/0.49          | ((X3) != (u1_struct_0 @ X0))
% 0.20/0.49          | ((X2) = (k6_tmap_1 @ X1 @ X3))
% 0.20/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.49          | ~ (l1_pre_topc @ X2)
% 0.20/0.49          | ~ (v2_pre_topc @ X2)
% 0.20/0.49          | ~ (v1_pre_topc @ X2)
% 0.20/0.49          | ~ (l1_pre_topc @ X1)
% 0.20/0.49          | ~ (v2_pre_topc @ X1)
% 0.20/0.49          | (v2_struct_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X1)
% 0.20/0.49          | ~ (v2_pre_topc @ X1)
% 0.20/0.49          | ~ (l1_pre_topc @ X1)
% 0.20/0.49          | ~ (v1_pre_topc @ (k8_tmap_1 @ X1 @ X0))
% 0.20/0.49          | ~ (v2_pre_topc @ (k8_tmap_1 @ X1 @ X0))
% 0.20/0.49          | ~ (l1_pre_topc @ (k8_tmap_1 @ X1 @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.49          | ((k8_tmap_1 @ X1 @ X0) = (k6_tmap_1 @ X1 @ (u1_struct_0 @ X0)))
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.49        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.49            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.49        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.49  thf('13', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k8_tmap_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.49         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.49         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X4)
% 0.20/0.49          | ~ (v2_pre_topc @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4)
% 0.20/0.49          | ~ (m1_pre_topc @ X5 @ X4)
% 0.20/0.49          | (l1_pre_topc @ (k8_tmap_1 @ X4 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.49  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X4)
% 0.20/0.49          | ~ (v2_pre_topc @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4)
% 0.20/0.49          | ~ (m1_pre_topc @ X5 @ X4)
% 0.20/0.49          | (v2_pre_topc @ (k8_tmap_1 @ X4 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.49  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.49        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13', '21', '29', '30', '31'])).
% 0.20/0.49  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.20/0.49            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.20/0.49      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (l1_pre_topc @ X4)
% 0.20/0.49          | ~ (v2_pre_topc @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4)
% 0.20/0.49          | ~ (m1_pre_topc @ X5 @ X4)
% 0.20/0.49          | (v1_pre_topc @ (k8_tmap_1 @ X4 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.49  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['34', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['44'])).
% 0.20/0.49  thf(t106_tmap_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.49             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.49               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7))
% 0.20/0.49              != (k6_tmap_1 @ X7 @ X6))
% 0.20/0.49          | (v3_pre_topc @ X6 @ X7)
% 0.20/0.49          | ~ (l1_pre_topc @ X7)
% 0.20/0.49          | ~ (v2_pre_topc @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t106_tmap_1])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 0.20/0.49           | (v2_struct_0 @ sk_A)
% 0.20/0.49           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.49           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 0.20/0.49           | (v2_struct_0 @ sk_A)
% 0.20/0.49           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.49           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.49         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      ((((v2_struct_0 @ sk_A) | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.49  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf(t16_tsep_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.49                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.49                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.49          | ((X10) != (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (v3_pre_topc @ X10 @ X9)
% 0.20/0.49          | (v1_tsep_1 @ X8 @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.49          | ~ (l1_pre_topc @ X9)
% 0.20/0.49          | ~ (v2_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X9)
% 0.20/0.49          | ~ (l1_pre_topc @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.20/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.49          | (v1_tsep_1 @ X8 @ X9)
% 0.20/0.49          | ~ (v3_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.20/0.49          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.20/0.49      inference('simplify', [status(thm)], ['58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.49        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.49        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['57', '59'])).
% 0.20/0.49  thf('61', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.49        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (((v1_tsep_1 @ sk_B @ sk_A))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['56', '64'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.49       ~
% 0.20/0.49       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.49       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['44'])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['44'])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.49          | ((X10) != (u1_struct_0 @ X8))
% 0.20/0.49          | ~ (v1_tsep_1 @ X8 @ X9)
% 0.20/0.49          | ~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.49          | (v3_pre_topc @ X10 @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.49          | ~ (l1_pre_topc @ X9)
% 0.20/0.49          | ~ (v2_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X9)
% 0.20/0.49          | ~ (l1_pre_topc @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.20/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.49          | (v3_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.20/0.49          | ~ (v1_tsep_1 @ X8 @ X9)
% 0.20/0.49          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.20/0.49      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.49        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.49        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['70', '72'])).
% 0.20/0.49  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.49        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.20/0.49         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '77'])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.49          | ~ (v3_pre_topc @ X6 @ X7)
% 0.20/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7))
% 0.20/0.49              = (k6_tmap_1 @ X7 @ X6))
% 0.20/0.49          | ~ (l1_pre_topc @ X7)
% 0.20/0.49          | ~ (v2_pre_topc @ X7)
% 0.20/0.49          | (v2_struct_0 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t106_tmap_1])).
% 0.20/0.49  thf('81', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.20/0.49        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.49  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['34', '42'])).
% 0.20/0.49  thf('85', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49            = (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.49        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.20/0.49  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('87', plain,
% 0.20/0.49      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.49        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49            = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('clc', [status(thm)], ['85', '86'])).
% 0.20/0.49  thf('88', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.49         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['78', '87'])).
% 0.20/0.49  thf('89', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('90', plain,
% 0.20/0.49      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.20/0.49             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.49       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['90'])).
% 0.20/0.49  thf('92', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['1', '4', '67', '68', '91'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
