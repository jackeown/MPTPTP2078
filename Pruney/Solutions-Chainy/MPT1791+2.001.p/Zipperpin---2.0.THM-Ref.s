%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ugnn4x1YIs

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:45 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 746 expanded)
%              Number of leaves         :   37 ( 227 expanded)
%              Depth                    :   26
%              Number of atoms          : 1926 (10258 expanded)
%              Number of equality atoms :   82 ( 400 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(t106_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k6_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_tmap_1])).

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r2_hidden @ X24 @ ( u1_pre_topc @ X25 ) )
      | ( ( u1_pre_topc @ X25 )
        = ( k5_tmap_1 @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X27 @ X26 ) )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( ~ ( v1_pre_topc @ X5 )
      | ( X5
        = ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( u1_pre_topc @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('28',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('31',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('39',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','36','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X27 @ X26 ) )
        = ( k5_tmap_1 @ X27 @ X26 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','53'])).

thf('55',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','54'])).

thf('56',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m2_connsp_2 @ ( k2_struct_0 @ X21 ) @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_connsp_2])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('69',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m2_connsp_2 @ X19 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_connsp_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X27 @ X26 ) )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X5: $i] :
      ( ~ ( v1_pre_topc @ X5 )
      | ( X5
        = ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( u1_pre_topc @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('83',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('85',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('86',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('93',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('94',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['83','91','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('102',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X27 @ X26 ) )
        = ( k5_tmap_1 @ X27 @ X26 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('111',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r2_hidden @ X24 @ ( u1_pre_topc @ X25 ) )
      | ( ( u1_pre_topc @ X25 )
        = ( k5_tmap_1 @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('118',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('119',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('120',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('121',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m2_connsp_2 @ ( k2_struct_0 @ X21 ) @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_connsp_2])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m2_connsp_2 @ ( k2_struct_0 @ X0 ) @ X0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('126',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('127',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m2_connsp_2 @ X16 @ X15 @ X14 )
      | ( r1_tarski @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k1_tops_1 @ X0 @ X1 ) )
      | ~ ( m2_connsp_2 @ X1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ ( k2_struct_0 @ X0 ) @ X0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('134',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('136',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('141',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['118','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('148',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v3_pre_topc @ X7 @ X8 )
      | ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('149',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('154',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('155',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','155','156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    r2_hidden @ ( k2_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','160'])).

thf('162',plain,
    ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','161'])).

thf('163',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('164',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('166',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','160'])).

thf('167',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['164','167'])).

thf('169',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('170',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( u1_pre_topc @ X25 )
       != ( k5_tmap_1 @ X25 @ X24 ) )
      | ( r2_hidden @ X24 @ ( u1_pre_topc @ X25 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','178'])).

thf('180',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X7 @ ( u1_pre_topc @ X8 ) )
      | ( v3_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('183',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','185'])).

thf('187',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('188',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ugnn4x1YIs
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:23:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.89/1.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.09  % Solved by: fo/fo7.sh
% 0.89/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.09  % done 427 iterations in 0.601s
% 0.89/1.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.09  % SZS output start Refutation
% 0.89/1.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.09  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.89/1.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.89/1.09  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.89/1.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.09  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.89/1.09  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.89/1.09  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.89/1.09  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.89/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.09  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.89/1.09  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.89/1.09  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.89/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.09  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.89/1.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.09  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.89/1.09  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.89/1.09  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.89/1.09  thf(t106_tmap_1, conjecture,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.09       ( ![B:$i]:
% 0.89/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.09           ( ( v3_pre_topc @ B @ A ) <=>
% 0.89/1.09             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.89/1.09               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.09    (~( ![A:$i]:
% 0.89/1.09        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.89/1.09            ( l1_pre_topc @ A ) ) =>
% 0.89/1.09          ( ![B:$i]:
% 0.89/1.09            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.09              ( ( v3_pre_topc @ B @ A ) <=>
% 0.89/1.09                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.89/1.09                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.89/1.09    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.89/1.09  thf('0', plain,
% 0.89/1.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('1', plain,
% 0.89/1.09      (~
% 0.89/1.09       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.89/1.09       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.09      inference('split', [status(esa)], ['0'])).
% 0.89/1.09  thf('2', plain,
% 0.89/1.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('3', plain,
% 0.89/1.09      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.09      inference('split', [status(esa)], ['2'])).
% 0.89/1.09  thf('4', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(d5_pre_topc, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( l1_pre_topc @ A ) =>
% 0.89/1.09       ( ![B:$i]:
% 0.89/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.09           ( ( v3_pre_topc @ B @ A ) <=>
% 0.89/1.09             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.89/1.09  thf('5', plain,
% 0.89/1.09      (![X7 : $i, X8 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.89/1.09          | ~ (v3_pre_topc @ X7 @ X8)
% 0.89/1.09          | (r2_hidden @ X7 @ (u1_pre_topc @ X8))
% 0.89/1.09          | ~ (l1_pre_topc @ X8))),
% 0.89/1.09      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.89/1.09  thf('6', plain,
% 0.89/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.89/1.09        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['4', '5'])).
% 0.89/1.09  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('8', plain,
% 0.89/1.09      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.89/1.09        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['6', '7'])).
% 0.89/1.09  thf('9', plain,
% 0.89/1.09      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.89/1.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['3', '8'])).
% 0.89/1.09  thf('10', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(t103_tmap_1, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.09       ( ![B:$i]:
% 0.89/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.09           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.89/1.09             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.09  thf('11', plain,
% 0.89/1.09      (![X24 : $i, X25 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.89/1.09          | ~ (r2_hidden @ X24 @ (u1_pre_topc @ X25))
% 0.89/1.09          | ((u1_pre_topc @ X25) = (k5_tmap_1 @ X25 @ X24))
% 0.89/1.09          | ~ (l1_pre_topc @ X25)
% 0.89/1.09          | ~ (v2_pre_topc @ X25)
% 0.89/1.09          | (v2_struct_0 @ X25))),
% 0.89/1.09      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.89/1.09  thf('12', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['10', '11'])).
% 0.89/1.09  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('15', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.89/1.09  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('17', plain,
% 0.89/1.09      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.89/1.09        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('clc', [status(thm)], ['15', '16'])).
% 0.89/1.09  thf('18', plain,
% 0.89/1.09      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.89/1.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['9', '17'])).
% 0.89/1.09  thf('19', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(t104_tmap_1, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.09       ( ![B:$i]:
% 0.89/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.09           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.89/1.09             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.09  thf('20', plain,
% 0.89/1.09      (![X26 : $i, X27 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.89/1.09          | ((u1_struct_0 @ (k6_tmap_1 @ X27 @ X26)) = (u1_struct_0 @ X27))
% 0.89/1.09          | ~ (l1_pre_topc @ X27)
% 0.89/1.09          | ~ (v2_pre_topc @ X27)
% 0.89/1.09          | (v2_struct_0 @ X27))),
% 0.89/1.09      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.89/1.09  thf('21', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.09  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('24', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.89/1.09  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('26', plain,
% 0.89/1.09      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.89/1.09      inference('clc', [status(thm)], ['24', '25'])).
% 0.89/1.09  thf(abstractness_v1_pre_topc, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( l1_pre_topc @ A ) =>
% 0.89/1.09       ( ( v1_pre_topc @ A ) =>
% 0.89/1.09         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.89/1.09  thf('27', plain,
% 0.89/1.09      (![X5 : $i]:
% 0.89/1.09         (~ (v1_pre_topc @ X5)
% 0.89/1.09          | ((X5) = (g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5)))
% 0.89/1.09          | ~ (l1_pre_topc @ X5))),
% 0.89/1.09      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.89/1.09  thf('28', plain,
% 0.89/1.09      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.89/1.09          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09             (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.89/1.09        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['26', '27'])).
% 0.89/1.09  thf('29', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(dt_k6_tmap_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.89/1.09         ( l1_pre_topc @ A ) & 
% 0.89/1.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.89/1.09       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.89/1.09         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.89/1.09         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.89/1.09  thf('30', plain,
% 0.89/1.09      (![X22 : $i, X23 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X22)
% 0.89/1.09          | ~ (v2_pre_topc @ X22)
% 0.89/1.09          | (v2_struct_0 @ X22)
% 0.89/1.09          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.89/1.09          | (l1_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.89/1.09  thf('31', plain,
% 0.89/1.09      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09        | (v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['29', '30'])).
% 0.89/1.09  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('34', plain,
% 0.89/1.09      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.89/1.09  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('36', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.89/1.09      inference('clc', [status(thm)], ['34', '35'])).
% 0.89/1.09  thf('37', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('38', plain,
% 0.89/1.09      (![X22 : $i, X23 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X22)
% 0.89/1.09          | ~ (v2_pre_topc @ X22)
% 0.89/1.09          | (v2_struct_0 @ X22)
% 0.89/1.09          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.89/1.09          | (v1_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.89/1.09  thf('39', plain,
% 0.89/1.09      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09        | (v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['37', '38'])).
% 0.89/1.09  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('42', plain,
% 0.89/1.09      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.89/1.09  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('44', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.89/1.09      inference('clc', [status(thm)], ['42', '43'])).
% 0.89/1.09  thf('45', plain,
% 0.89/1.09      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.89/1.09         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09            (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.89/1.09      inference('demod', [status(thm)], ['28', '36', '44'])).
% 0.89/1.09  thf('46', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('47', plain,
% 0.89/1.09      (![X26 : $i, X27 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.89/1.09          | ((u1_pre_topc @ (k6_tmap_1 @ X27 @ X26)) = (k5_tmap_1 @ X27 @ X26))
% 0.89/1.09          | ~ (l1_pre_topc @ X27)
% 0.89/1.09          | ~ (v2_pre_topc @ X27)
% 0.89/1.09          | (v2_struct_0 @ X27))),
% 0.89/1.09      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.89/1.09  thf('48', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['46', '47'])).
% 0.89/1.09  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('51', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.89/1.09  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('53', plain,
% 0.89/1.09      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.89/1.09      inference('clc', [status(thm)], ['51', '52'])).
% 0.89/1.09  thf('54', plain,
% 0.89/1.09      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.89/1.09         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('demod', [status(thm)], ['45', '53'])).
% 0.89/1.09  thf('55', plain,
% 0.89/1.09      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.89/1.09          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.89/1.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['18', '54'])).
% 0.89/1.09  thf('56', plain,
% 0.89/1.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.89/1.09      inference('split', [status(esa)], ['0'])).
% 0.89/1.09  thf('57', plain,
% 0.89/1.09      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.89/1.09             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['55', '56'])).
% 0.89/1.09  thf('58', plain,
% 0.89/1.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.89/1.09       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.09      inference('simplify', [status(thm)], ['57'])).
% 0.89/1.09  thf('59', plain,
% 0.89/1.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.89/1.09       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.09      inference('split', [status(esa)], ['2'])).
% 0.89/1.09  thf('60', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(t35_connsp_2, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.09       ( ![B:$i]:
% 0.89/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.09           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.89/1.09  thf('61', plain,
% 0.89/1.09      (![X20 : $i, X21 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.89/1.09          | (m2_connsp_2 @ (k2_struct_0 @ X21) @ X21 @ X20)
% 0.89/1.09          | ~ (l1_pre_topc @ X21)
% 0.89/1.09          | ~ (v2_pre_topc @ X21)
% 0.89/1.09          | (v2_struct_0 @ X21))),
% 0.89/1.09      inference('cnf', [status(esa)], [t35_connsp_2])).
% 0.89/1.09  thf('62', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.89/1.09      inference('sup-', [status(thm)], ['60', '61'])).
% 0.89/1.09  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('65', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.89/1.09      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.89/1.09  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('67', plain, ((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.89/1.09      inference('clc', [status(thm)], ['65', '66'])).
% 0.89/1.09  thf('68', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(dt_m2_connsp_2, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.89/1.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.89/1.09       ( ![C:$i]:
% 0.89/1.09         ( ( m2_connsp_2 @ C @ A @ B ) =>
% 0.89/1.09           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.89/1.09  thf('69', plain,
% 0.89/1.09      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X17)
% 0.89/1.09          | ~ (v2_pre_topc @ X17)
% 0.89/1.09          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.89/1.09          | (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.89/1.09          | ~ (m2_connsp_2 @ X19 @ X17 @ X18))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_m2_connsp_2])).
% 0.89/1.09  thf('70', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.89/1.09          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.09          | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09          | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['68', '69'])).
% 0.89/1.09  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('73', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.89/1.09          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.89/1.09      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.89/1.09  thf('74', plain,
% 0.89/1.09      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['67', '73'])).
% 0.89/1.09  thf('75', plain,
% 0.89/1.09      (![X26 : $i, X27 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.89/1.09          | ((u1_struct_0 @ (k6_tmap_1 @ X27 @ X26)) = (u1_struct_0 @ X27))
% 0.89/1.09          | ~ (l1_pre_topc @ X27)
% 0.89/1.09          | ~ (v2_pre_topc @ X27)
% 0.89/1.09          | (v2_struct_0 @ X27))),
% 0.89/1.09      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.89/1.09  thf('76', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09            = (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['74', '75'])).
% 0.89/1.09  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('79', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09            = (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.89/1.09  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('81', plain,
% 0.89/1.09      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09         = (u1_struct_0 @ sk_A))),
% 0.89/1.09      inference('clc', [status(thm)], ['79', '80'])).
% 0.89/1.09  thf('82', plain,
% 0.89/1.09      (![X5 : $i]:
% 0.89/1.09         (~ (v1_pre_topc @ X5)
% 0.89/1.09          | ((X5) = (g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5)))
% 0.89/1.09          | ~ (l1_pre_topc @ X5))),
% 0.89/1.09      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.89/1.09  thf('83', plain,
% 0.89/1.09      ((((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.89/1.09          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09             (u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))))
% 0.89/1.09        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['81', '82'])).
% 0.89/1.09  thf('84', plain,
% 0.89/1.09      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['67', '73'])).
% 0.89/1.09  thf('85', plain,
% 0.89/1.09      (![X22 : $i, X23 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X22)
% 0.89/1.09          | ~ (v2_pre_topc @ X22)
% 0.89/1.09          | (v2_struct_0 @ X22)
% 0.89/1.09          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.89/1.09          | (l1_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.89/1.09  thf('86', plain,
% 0.89/1.09      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09        | (v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['84', '85'])).
% 0.89/1.09  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('89', plain,
% 0.89/1.09      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09        | (v2_struct_0 @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.89/1.09  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('91', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.89/1.09      inference('clc', [status(thm)], ['89', '90'])).
% 0.89/1.09  thf('92', plain,
% 0.89/1.09      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['67', '73'])).
% 0.89/1.09  thf('93', plain,
% 0.89/1.09      (![X22 : $i, X23 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X22)
% 0.89/1.09          | ~ (v2_pre_topc @ X22)
% 0.89/1.09          | (v2_struct_0 @ X22)
% 0.89/1.09          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.89/1.09          | (v1_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.89/1.09  thf('94', plain,
% 0.89/1.09      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09        | (v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['92', '93'])).
% 0.89/1.09  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('97', plain,
% 0.89/1.09      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09        | (v2_struct_0 @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.89/1.09  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('99', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.89/1.09      inference('clc', [status(thm)], ['97', '98'])).
% 0.89/1.09  thf('100', plain,
% 0.89/1.09      (((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.89/1.09         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09            (u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 0.89/1.09      inference('demod', [status(thm)], ['83', '91', '99'])).
% 0.89/1.09  thf('101', plain,
% 0.89/1.09      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['67', '73'])).
% 0.89/1.09  thf('102', plain,
% 0.89/1.09      (![X26 : $i, X27 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.89/1.09          | ((u1_pre_topc @ (k6_tmap_1 @ X27 @ X26)) = (k5_tmap_1 @ X27 @ X26))
% 0.89/1.09          | ~ (l1_pre_topc @ X27)
% 0.89/1.09          | ~ (v2_pre_topc @ X27)
% 0.89/1.09          | (v2_struct_0 @ X27))),
% 0.89/1.09      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.89/1.09  thf('103', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09            = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['101', '102'])).
% 0.89/1.09  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('106', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09            = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.89/1.09      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.89/1.09  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('108', plain,
% 0.89/1.09      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09         = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.89/1.09      inference('clc', [status(thm)], ['106', '107'])).
% 0.89/1.09  thf('109', plain,
% 0.89/1.09      (((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.89/1.09         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09            (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.89/1.09      inference('demod', [status(thm)], ['100', '108'])).
% 0.89/1.09  thf('110', plain,
% 0.89/1.09      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['67', '73'])).
% 0.89/1.09  thf('111', plain,
% 0.89/1.09      (![X24 : $i, X25 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.89/1.09          | ~ (r2_hidden @ X24 @ (u1_pre_topc @ X25))
% 0.89/1.09          | ((u1_pre_topc @ X25) = (k5_tmap_1 @ X25 @ X24))
% 0.89/1.09          | ~ (l1_pre_topc @ X25)
% 0.89/1.09          | ~ (v2_pre_topc @ X25)
% 0.89/1.09          | (v2_struct_0 @ X25))),
% 0.89/1.09      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.89/1.09  thf('112', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09        | ~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['110', '111'])).
% 0.89/1.09  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('115', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09        | ~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.89/1.09  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('117', plain,
% 0.89/1.09      ((~ (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.89/1.09      inference('clc', [status(thm)], ['115', '116'])).
% 0.89/1.09  thf(d3_struct_0, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.89/1.09  thf('118', plain,
% 0.89/1.09      (![X6 : $i]:
% 0.89/1.09         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.09  thf(dt_k2_subset_1, axiom,
% 0.89/1.09    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.89/1.09  thf('119', plain,
% 0.89/1.09      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.89/1.09  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.89/1.09  thf('120', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.89/1.09      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.89/1.09  thf('121', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.89/1.09      inference('demod', [status(thm)], ['119', '120'])).
% 0.89/1.09  thf('122', plain,
% 0.89/1.09      (![X20 : $i, X21 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.89/1.09          | (m2_connsp_2 @ (k2_struct_0 @ X21) @ X21 @ X20)
% 0.89/1.09          | ~ (l1_pre_topc @ X21)
% 0.89/1.09          | ~ (v2_pre_topc @ X21)
% 0.89/1.09          | (v2_struct_0 @ X21))),
% 0.89/1.09      inference('cnf', [status(esa)], [t35_connsp_2])).
% 0.89/1.09  thf('123', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v2_struct_0 @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | (m2_connsp_2 @ (k2_struct_0 @ X0) @ X0 @ (u1_struct_0 @ X0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['121', '122'])).
% 0.89/1.09  thf('124', plain,
% 0.89/1.09      (![X6 : $i]:
% 0.89/1.09         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.09  thf('125', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.89/1.09      inference('demod', [status(thm)], ['119', '120'])).
% 0.89/1.09  thf('126', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.89/1.09      inference('demod', [status(thm)], ['119', '120'])).
% 0.89/1.09  thf(d2_connsp_2, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.09       ( ![B:$i]:
% 0.89/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.09           ( ![C:$i]:
% 0.89/1.09             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.09               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.89/1.09                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.89/1.09  thf('127', plain,
% 0.89/1.09      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.89/1.09          | ~ (m2_connsp_2 @ X16 @ X15 @ X14)
% 0.89/1.09          | (r1_tarski @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.89/1.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.89/1.09          | ~ (l1_pre_topc @ X15)
% 0.89/1.09          | ~ (v2_pre_topc @ X15))),
% 0.89/1.09      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.89/1.09  thf('128', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (v2_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.89/1.09          | (r1_tarski @ (u1_struct_0 @ X0) @ (k1_tops_1 @ X0 @ X1))
% 0.89/1.09          | ~ (m2_connsp_2 @ X1 @ X0 @ (u1_struct_0 @ X0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['126', '127'])).
% 0.89/1.09  thf('129', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (m2_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ (u1_struct_0 @ X0))
% 0.89/1.09          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.89/1.09             (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['125', '128'])).
% 0.89/1.09  thf('130', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (m2_connsp_2 @ (k2_struct_0 @ X0) @ X0 @ (u1_struct_0 @ X0))
% 0.89/1.09          | ~ (l1_struct_0 @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.89/1.09             (k1_tops_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['124', '129'])).
% 0.89/1.09  thf('131', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | (v2_struct_0 @ X0)
% 0.89/1.09          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.89/1.09             (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_struct_0 @ X0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['123', '130'])).
% 0.89/1.09  thf('132', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (l1_struct_0 @ X0)
% 0.89/1.09          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.89/1.09             (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.89/1.09          | (v2_struct_0 @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['131'])).
% 0.89/1.09  thf('133', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.89/1.09      inference('demod', [status(thm)], ['119', '120'])).
% 0.89/1.09  thf(t44_tops_1, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( l1_pre_topc @ A ) =>
% 0.89/1.09       ( ![B:$i]:
% 0.89/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.09           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.89/1.09  thf('134', plain,
% 0.89/1.09      (![X12 : $i, X13 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.89/1.09          | (r1_tarski @ (k1_tops_1 @ X13 @ X12) @ X12)
% 0.89/1.09          | ~ (l1_pre_topc @ X13))),
% 0.89/1.09      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.89/1.09  thf('135', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X0)
% 0.89/1.09          | (r1_tarski @ (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.89/1.09             (u1_struct_0 @ X0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['133', '134'])).
% 0.89/1.09  thf(d10_xboole_0, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.09  thf('136', plain,
% 0.89/1.09      (![X0 : $i, X2 : $i]:
% 0.89/1.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.09  thf('137', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.89/1.09               (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.89/1.09          | ((u1_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['135', '136'])).
% 0.89/1.09  thf('138', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | (v2_struct_0 @ X0)
% 0.89/1.09          | ~ (l1_struct_0 @ X0)
% 0.89/1.09          | ((u1_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.89/1.09          | ~ (l1_pre_topc @ X0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['132', '137'])).
% 0.89/1.09  thf('139', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((u1_struct_0 @ X0) = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.89/1.09          | ~ (l1_struct_0 @ X0)
% 0.89/1.09          | (v2_struct_0 @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['138'])).
% 0.89/1.09  thf('140', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.89/1.09      inference('demod', [status(thm)], ['119', '120'])).
% 0.89/1.09  thf(fc9_tops_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.89/1.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.89/1.09       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.89/1.09  thf('141', plain,
% 0.89/1.09      (![X10 : $i, X11 : $i]:
% 0.89/1.09         (~ (l1_pre_topc @ X10)
% 0.89/1.09          | ~ (v2_pre_topc @ X10)
% 0.89/1.09          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.89/1.09          | (v3_pre_topc @ (k1_tops_1 @ X10 @ X11) @ X10))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.89/1.09  thf('142', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v3_pre_topc @ (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['140', '141'])).
% 0.89/1.09  thf('143', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | (v2_struct_0 @ X0)
% 0.89/1.09          | ~ (l1_struct_0 @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['139', '142'])).
% 0.89/1.09  thf('144', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (l1_struct_0 @ X0)
% 0.89/1.09          | (v2_struct_0 @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['143'])).
% 0.89/1.09  thf('145', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.89/1.09          | ~ (l1_struct_0 @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | (v2_struct_0 @ X0)
% 0.89/1.09          | ~ (l1_struct_0 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['118', '144'])).
% 0.89/1.09  thf('146', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v2_struct_0 @ X0)
% 0.89/1.09          | ~ (v2_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_pre_topc @ X0)
% 0.89/1.09          | ~ (l1_struct_0 @ X0)
% 0.89/1.09          | (v3_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['145'])).
% 0.89/1.09  thf('147', plain,
% 0.89/1.09      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.89/1.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['67', '73'])).
% 0.89/1.09  thf('148', plain,
% 0.89/1.09      (![X7 : $i, X8 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.89/1.09          | ~ (v3_pre_topc @ X7 @ X8)
% 0.89/1.09          | (r2_hidden @ X7 @ (u1_pre_topc @ X8))
% 0.89/1.09          | ~ (l1_pre_topc @ X8))),
% 0.89/1.09      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.89/1.09  thf('149', plain,
% 0.89/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['147', '148'])).
% 0.89/1.09  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('151', plain,
% 0.89/1.09      (((r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['149', '150'])).
% 0.89/1.09  thf('152', plain,
% 0.89/1.09      ((~ (l1_struct_0 @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | (v2_struct_0 @ sk_A)
% 0.89/1.09        | (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['146', '151'])).
% 0.89/1.09  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(dt_l1_pre_topc, axiom,
% 0.89/1.09    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.89/1.09  thf('154', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.09  thf('155', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.09      inference('sup-', [status(thm)], ['153', '154'])).
% 0.89/1.09  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('158', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | (r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['152', '155', '156', '157'])).
% 0.89/1.09  thf('159', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('160', plain,
% 0.89/1.09      ((r2_hidden @ (k2_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.89/1.09      inference('clc', [status(thm)], ['158', '159'])).
% 0.89/1.09  thf('161', plain,
% 0.89/1.09      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['117', '160'])).
% 0.89/1.09  thf('162', plain,
% 0.89/1.09      (((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.89/1.09         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['109', '161'])).
% 0.89/1.09  thf('163', plain,
% 0.89/1.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.89/1.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.89/1.09      inference('split', [status(esa)], ['2'])).
% 0.89/1.09  thf('164', plain,
% 0.89/1.09      ((((k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.89/1.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['162', '163'])).
% 0.89/1.09  thf('165', plain,
% 0.89/1.09      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09         = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.89/1.09      inference('clc', [status(thm)], ['106', '107'])).
% 0.89/1.09  thf('166', plain,
% 0.89/1.09      (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['117', '160'])).
% 0.89/1.09  thf('167', plain,
% 0.89/1.09      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.89/1.09         = (u1_pre_topc @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['165', '166'])).
% 0.89/1.09  thf('168', plain,
% 0.89/1.09      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_pre_topc @ sk_A)))
% 0.89/1.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['164', '167'])).
% 0.89/1.09  thf('169', plain,
% 0.89/1.09      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.89/1.09      inference('clc', [status(thm)], ['51', '52'])).
% 0.89/1.09  thf('170', plain,
% 0.89/1.09      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.89/1.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['168', '169'])).
% 0.89/1.09  thf('171', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('172', plain,
% 0.89/1.09      (![X24 : $i, X25 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.89/1.09          | ((u1_pre_topc @ X25) != (k5_tmap_1 @ X25 @ X24))
% 0.89/1.09          | (r2_hidden @ X24 @ (u1_pre_topc @ X25))
% 0.89/1.09          | ~ (l1_pre_topc @ X25)
% 0.89/1.09          | ~ (v2_pre_topc @ X25)
% 0.89/1.09          | (v2_struct_0 @ X25))),
% 0.89/1.09      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.89/1.09  thf('173', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.89/1.09        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['171', '172'])).
% 0.89/1.09  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('176', plain,
% 0.89/1.09      (((v2_struct_0 @ sk_A)
% 0.89/1.09        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.89/1.09        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('demod', [status(thm)], ['173', '174', '175'])).
% 0.89/1.09  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('178', plain,
% 0.89/1.09      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.89/1.09        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('clc', [status(thm)], ['176', '177'])).
% 0.89/1.09  thf('179', plain,
% 0.89/1.09      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.89/1.09         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.89/1.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['170', '178'])).
% 0.89/1.09  thf('180', plain,
% 0.89/1.09      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.89/1.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.89/1.09      inference('simplify', [status(thm)], ['179'])).
% 0.89/1.09  thf('181', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('182', plain,
% 0.89/1.09      (![X7 : $i, X8 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.89/1.09          | ~ (r2_hidden @ X7 @ (u1_pre_topc @ X8))
% 0.89/1.09          | (v3_pre_topc @ X7 @ X8)
% 0.89/1.09          | ~ (l1_pre_topc @ X8))),
% 0.89/1.09      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.89/1.09  thf('183', plain,
% 0.89/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.09        | (v3_pre_topc @ sk_B @ sk_A)
% 0.89/1.09        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['181', '182'])).
% 0.89/1.09  thf('184', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('185', plain,
% 0.89/1.09      (((v3_pre_topc @ sk_B @ sk_A)
% 0.89/1.09        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['183', '184'])).
% 0.89/1.09  thf('186', plain,
% 0.89/1.09      (((v3_pre_topc @ sk_B @ sk_A))
% 0.89/1.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['180', '185'])).
% 0.89/1.09  thf('187', plain,
% 0.89/1.09      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.09      inference('split', [status(esa)], ['0'])).
% 0.89/1.09  thf('188', plain,
% 0.89/1.09      (~
% 0.89/1.09       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.89/1.09          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.89/1.09       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['186', '187'])).
% 0.89/1.09  thf('189', plain, ($false),
% 0.89/1.09      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '188'])).
% 0.89/1.09  
% 0.89/1.09  % SZS output end Refutation
% 0.89/1.09  
% 0.89/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
