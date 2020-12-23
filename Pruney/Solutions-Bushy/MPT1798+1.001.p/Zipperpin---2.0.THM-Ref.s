%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1798+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EZ0gOaOMhf

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  153 (1344 expanded)
%              Number of leaves         :   24 ( 395 expanded)
%              Depth                    :   18
%              Number of atoms          : 1514 (27241 expanded)
%              Number of equality atoms :  112 (1998 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

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

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k5_tmap_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_tmap_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('14',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( g1_pre_topc @ X13 @ X14 )
       != ( g1_pre_topc @ X11 @ X12 ) )
      | ( X14 = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
       != ( g1_pre_topc @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k6_tmap_1 @ X6 @ X5 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( k5_tmap_1 @ X6 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( X3
       != ( k8_tmap_1 @ X2 @ X1 ) )
      | ( X4
       != ( u1_struct_0 @ X1 ) )
      | ( X3
        = ( k6_tmap_1 @ X2 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( v1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X2 @ X1 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X2 @ X1 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( ( k8_tmap_1 @ X2 @ X1 )
        = ( k6_tmap_1 @ X2 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('31',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('39',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('47',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','36','44','52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('62',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('63',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('64',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('65',plain,
    ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','60','61','62','63','64'])).

thf('66',plain,(
    m1_subset_1 @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','65'])).

thf('67',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( g1_pre_topc @ X13 @ X14 )
       != ( g1_pre_topc @ X11 @ X12 ) )
      | ( X13 = X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('70',plain,
    ( ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','60','61','62','63','64'])).

thf('71',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','72'])).

thf('74',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('76',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect+',[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,
    ( ( sk_C
      = ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['78'])).

thf('81',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['83'])).

thf('86',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k6_tmap_1 @ X6 @ X5 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( k5_tmap_1 @ X6 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( k6_tmap_1 @ sk_A @ sk_C )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k6_tmap_1 @ sk_A @ sk_C )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('94',plain,
    ( ( sk_C
      = ( u1_struct_0 @ sk_B ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['78'])).

thf('95',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k5_tmap_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_tmap_1])).

thf('98',plain,
    ( ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( g1_pre_topc @ X13 @ X14 )
       != ( g1_pre_topc @ X11 @ X12 ) )
      | ( X14 = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('105',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k5_tmap_1 @ sk_A @ sk_C )
          = X0 )
        | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) )
         != ( g1_pre_topc @ X1 @ X0 ) ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) )
         != X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v1_pre_topc @ X0 )
        | ( ( k5_tmap_1 @ sk_A @ sk_C )
          = ( u1_pre_topc @ X0 ) ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','105'])).

thf('107',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_C )
        = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) )
      | ( ( k5_tmap_1 @ sk_A @ sk_C )
        = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) ) ) )
   <= ( ( sk_C
        = ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['92','107'])).

thf('109',plain,
    ( ( sk_C
      = ( u1_struct_0 @ sk_B ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['78'])).

thf('110',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('111',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ sk_C ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('113',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('115',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ sk_C ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('116',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('117',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('119',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_C )
      = ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) ) )
   <= ( ( sk_C
        = ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['108','113','114','117','118'])).

thf('120',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ sk_C ) )
   <= ( sk_C
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('121',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) )
   <= ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['81'])).

thf('122',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_C ) )
     != ( k5_tmap_1 @ sk_A @ sk_C ) )
   <= ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
       != ( k5_tmap_1 @ sk_A @ sk_C ) )
      & ( sk_C
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_C )
     != ( k5_tmap_1 @ sk_A @ sk_C ) )
   <= ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
       != ( k5_tmap_1 @ sk_A @ sk_C ) )
      & ( sk_C
        = ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,
    ( ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_C
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['80','82','84','124'])).

thf('126',plain,(
    ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['79','125'])).

thf('127',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','126'])).


%------------------------------------------------------------------------------
