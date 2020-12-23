%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cIlaB6JfBU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:45 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 354 expanded)
%              Number of leaves         :   34 ( 115 expanded)
%              Depth                    :   29
%              Number of atoms          : 1700 (4598 expanded)
%              Number of equality atoms :   88 ( 209 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
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
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
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
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X15: $i] :
      ( ~ ( v1_pre_topc @ X15 )
      | ( X15
        = ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('28',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
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
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
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
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['28','36','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['45','53'])).

thf('55',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','54'])).

thf('56',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('60',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X7: $i] :
      ( v1_xboole_0 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('66',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('74',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('79',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('84',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r2_hidden @ X24 @ ( u1_pre_topc @ X25 ) )
      | ( ( u1_pre_topc @ X25 )
        = ( k5_tmap_1 @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('89',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X27 @ X26 ) )
        = ( k5_tmap_1 @ X27 @ X26 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_tmap_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_tmap_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('94',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('95',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('98',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('101',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X27 @ X26 ) )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X15: $i] :
      ( ~ ( v1_pre_topc @ X15 )
      | ( X15
        = ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ k1_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ k1_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ k1_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k6_tmap_1 @ X0 @ k1_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['96','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ k1_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ k1_xboole_0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ k1_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ k1_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ k1_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ k1_xboole_0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ k1_xboole_0 )
        = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['91','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ k1_xboole_0 )
        = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( k6_tmap_1 @ sk_A @ k1_xboole_0 )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('120',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ k1_xboole_0 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ k1_xboole_0 )
        = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['90','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ k1_xboole_0 )
        = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( k5_tmap_1 @ sk_A @ k1_xboole_0 )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( u1_pre_topc @ X25 )
       != ( k5_tmap_1 @ X25 @ X24 ) )
      | ( r2_hidden @ X24 @ ( u1_pre_topc @ X25 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( k5_tmap_1 @ sk_A @ k1_xboole_0 ) )
      | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['126','134'])).

thf('136',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ( v3_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('150',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cIlaB6JfBU
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:03:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.99/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.16  % Solved by: fo/fo7.sh
% 0.99/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.16  % done 1165 iterations in 0.706s
% 0.99/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.16  % SZS output start Refutation
% 0.99/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.99/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.16  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.99/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.16  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.99/1.16  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.99/1.16  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.99/1.16  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.16  thf(sk_B_type, type, sk_B: $i > $i).
% 0.99/1.16  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.99/1.16  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.99/1.16  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.16  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.99/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.16  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.99/1.16  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.99/1.16  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.99/1.16  thf(t106_tmap_1, conjecture,
% 0.99/1.16    (![A:$i]:
% 0.99/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.16       ( ![B:$i]:
% 0.99/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.16           ( ( v3_pre_topc @ B @ A ) <=>
% 0.99/1.16             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.99/1.16               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.16    (~( ![A:$i]:
% 0.99/1.16        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.99/1.16            ( l1_pre_topc @ A ) ) =>
% 0.99/1.16          ( ![B:$i]:
% 0.99/1.16            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.16              ( ( v3_pre_topc @ B @ A ) <=>
% 0.99/1.16                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.99/1.16                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.99/1.16    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.99/1.16  thf('0', plain,
% 0.99/1.16      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.16          != (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.16        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('1', plain,
% 0.99/1.16      (~
% 0.99/1.16       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.16          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.99/1.16       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.99/1.16      inference('split', [status(esa)], ['0'])).
% 0.99/1.16  thf('2', plain,
% 0.99/1.16      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.16          = (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.16        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('3', plain,
% 0.99/1.16      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.99/1.16      inference('split', [status(esa)], ['2'])).
% 0.99/1.16  thf('4', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(d5_pre_topc, axiom,
% 0.99/1.16    (![A:$i]:
% 0.99/1.16     ( ( l1_pre_topc @ A ) =>
% 0.99/1.16       ( ![B:$i]:
% 0.99/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.16           ( ( v3_pre_topc @ B @ A ) <=>
% 0.99/1.16             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.99/1.16  thf('5', plain,
% 0.99/1.16      (![X16 : $i, X17 : $i]:
% 0.99/1.16         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.99/1.16          | ~ (v3_pre_topc @ X16 @ X17)
% 0.99/1.16          | (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.99/1.16          | ~ (l1_pre_topc @ X17))),
% 0.99/1.16      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.99/1.16  thf('6', plain,
% 0.99/1.16      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.16        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.99/1.16        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.99/1.16      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.16  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('8', plain,
% 0.99/1.16      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.99/1.16        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.99/1.16      inference('demod', [status(thm)], ['6', '7'])).
% 0.99/1.16  thf('9', plain,
% 0.99/1.16      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))
% 0.99/1.16         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['3', '8'])).
% 0.99/1.16  thf('10', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(t103_tmap_1, axiom,
% 0.99/1.16    (![A:$i]:
% 0.99/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.16       ( ![B:$i]:
% 0.99/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.16           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.99/1.16             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.16  thf('11', plain,
% 0.99/1.16      (![X24 : $i, X25 : $i]:
% 0.99/1.16         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.99/1.16          | ~ (r2_hidden @ X24 @ (u1_pre_topc @ X25))
% 0.99/1.16          | ((u1_pre_topc @ X25) = (k5_tmap_1 @ X25 @ X24))
% 0.99/1.16          | ~ (l1_pre_topc @ X25)
% 0.99/1.16          | ~ (v2_pre_topc @ X25)
% 0.99/1.16          | (v2_struct_0 @ X25))),
% 0.99/1.16      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.99/1.16  thf('12', plain,
% 0.99/1.16      (((v2_struct_0 @ sk_A)
% 0.99/1.16        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.16        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.16        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.16        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['10', '11'])).
% 0.99/1.16  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('15', plain,
% 0.99/1.16      (((v2_struct_0 @ sk_A)
% 0.99/1.16        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.16        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.99/1.16      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.99/1.16  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('17', plain,
% 0.99/1.16      ((~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.99/1.16        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.99/1.16      inference('clc', [status(thm)], ['15', '16'])).
% 0.99/1.16  thf('18', plain,
% 0.99/1.16      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1)))
% 0.99/1.16         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['9', '17'])).
% 0.99/1.16  thf('19', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(t104_tmap_1, axiom,
% 0.99/1.16    (![A:$i]:
% 0.99/1.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.16       ( ![B:$i]:
% 0.99/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.16           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.99/1.16             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.16  thf('20', plain,
% 0.99/1.16      (![X26 : $i, X27 : $i]:
% 0.99/1.16         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.16          | ((u1_struct_0 @ (k6_tmap_1 @ X27 @ X26)) = (u1_struct_0 @ X27))
% 0.99/1.16          | ~ (l1_pre_topc @ X27)
% 0.99/1.16          | ~ (v2_pre_topc @ X27)
% 0.99/1.16          | (v2_struct_0 @ X27))),
% 0.99/1.16      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.99/1.16  thf('21', plain,
% 0.99/1.16      (((v2_struct_0 @ sk_A)
% 0.99/1.16        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.16        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['19', '20'])).
% 0.99/1.17  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('24', plain,
% 0.99/1.17      (((v2_struct_0 @ sk_A)
% 0.99/1.17        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.99/1.17  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('26', plain,
% 0.99/1.17      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.99/1.17      inference('clc', [status(thm)], ['24', '25'])).
% 0.99/1.17  thf(abstractness_v1_pre_topc, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ( v1_pre_topc @ A ) =>
% 0.99/1.17         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.99/1.17  thf('27', plain,
% 0.99/1.17      (![X15 : $i]:
% 0.99/1.17         (~ (v1_pre_topc @ X15)
% 0.99/1.17          | ((X15) = (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.99/1.17          | ~ (l1_pre_topc @ X15))),
% 0.99/1.17      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.99/1.17  thf('28', plain,
% 0.99/1.17      ((((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.99/1.17          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17             (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))))
% 0.99/1.17        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['26', '27'])).
% 0.99/1.17  thf('29', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(dt_k6_tmap_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.99/1.17         ( l1_pre_topc @ A ) & 
% 0.99/1.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.17       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.99/1.17         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.99/1.17         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.99/1.17  thf('30', plain,
% 0.99/1.17      (![X22 : $i, X23 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X22)
% 0.99/1.17          | ~ (v2_pre_topc @ X22)
% 0.99/1.17          | (v2_struct_0 @ X22)
% 0.99/1.17          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.99/1.17          | (l1_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.99/1.17  thf('31', plain,
% 0.99/1.17      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17        | (v2_struct_0 @ sk_A)
% 0.99/1.17        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['29', '30'])).
% 0.99/1.17  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('34', plain,
% 0.99/1.17      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.99/1.17  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('36', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.99/1.17      inference('clc', [status(thm)], ['34', '35'])).
% 0.99/1.17  thf('37', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('38', plain,
% 0.99/1.17      (![X22 : $i, X23 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X22)
% 0.99/1.17          | ~ (v2_pre_topc @ X22)
% 0.99/1.17          | (v2_struct_0 @ X22)
% 0.99/1.17          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.99/1.17          | (v1_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.99/1.17  thf('39', plain,
% 0.99/1.17      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17        | (v2_struct_0 @ sk_A)
% 0.99/1.17        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['37', '38'])).
% 0.99/1.17  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('42', plain,
% 0.99/1.17      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.99/1.17  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('44', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.99/1.17      inference('clc', [status(thm)], ['42', '43'])).
% 0.99/1.17  thf('45', plain,
% 0.99/1.17      (((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.99/1.17         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.17            (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('demod', [status(thm)], ['28', '36', '44'])).
% 0.99/1.17  thf('46', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('47', plain,
% 0.99/1.17      (![X26 : $i, X27 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.17          | ((u1_pre_topc @ (k6_tmap_1 @ X27 @ X26)) = (k5_tmap_1 @ X27 @ X26))
% 0.99/1.17          | ~ (l1_pre_topc @ X27)
% 0.99/1.17          | ~ (v2_pre_topc @ X27)
% 0.99/1.17          | (v2_struct_0 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.99/1.17  thf('48', plain,
% 0.99/1.17      (((v2_struct_0 @ sk_A)
% 0.99/1.17        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17            = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['46', '47'])).
% 0.99/1.17  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('51', plain,
% 0.99/1.17      (((v2_struct_0 @ sk_A)
% 0.99/1.17        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17            = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.99/1.17      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.99/1.17  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('53', plain,
% 0.99/1.17      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17         = (k5_tmap_1 @ sk_A @ sk_B_1))),
% 0.99/1.17      inference('clc', [status(thm)], ['51', '52'])).
% 0.99/1.17  thf('54', plain,
% 0.99/1.17      (((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.99/1.17         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.99/1.17      inference('demod', [status(thm)], ['45', '53'])).
% 0.99/1.17  thf('55', plain,
% 0.99/1.17      ((((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.99/1.17          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.99/1.17         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['18', '54'])).
% 0.99/1.17  thf('56', plain,
% 0.99/1.17      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17          != (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.99/1.17         <= (~
% 0.99/1.17             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('split', [status(esa)], ['0'])).
% 0.99/1.17  thf('57', plain,
% 0.99/1.17      ((((k6_tmap_1 @ sk_A @ sk_B_1) != (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.99/1.17         <= (~
% 0.99/1.17             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.99/1.17             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['55', '56'])).
% 0.99/1.17  thf('58', plain,
% 0.99/1.17      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.99/1.17       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.99/1.17      inference('simplify', [status(thm)], ['57'])).
% 0.99/1.17  thf('59', plain,
% 0.99/1.17      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.99/1.17       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.99/1.17      inference('split', [status(esa)], ['2'])).
% 0.99/1.17  thf(t4_subset_1, axiom,
% 0.99/1.17    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.99/1.17  thf('60', plain,
% 0.99/1.17      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.17  thf(t44_tops_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( l1_pre_topc @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.17           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.99/1.17  thf('61', plain,
% 0.99/1.17      (![X20 : $i, X21 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.99/1.17          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ X20)
% 0.99/1.17          | ~ (l1_pre_topc @ X21))),
% 0.99/1.17      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.99/1.17  thf('62', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['60', '61'])).
% 0.99/1.17  thf(rc2_subset_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ?[B:$i]:
% 0.99/1.17       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.99/1.17  thf('63', plain, (![X7 : $i]: (v1_xboole_0 @ (sk_B @ X7))),
% 0.99/1.17      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.99/1.17  thf(d3_tarski, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( r1_tarski @ A @ B ) <=>
% 0.99/1.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.99/1.17  thf('64', plain,
% 0.99/1.17      (![X1 : $i, X3 : $i]:
% 0.99/1.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.99/1.17  thf('65', plain,
% 0.99/1.17      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.17  thf(t5_subset, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.99/1.17          ( v1_xboole_0 @ C ) ) ))).
% 0.99/1.17  thf('66', plain,
% 0.99/1.17      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.99/1.17         (~ (r2_hidden @ X12 @ X13)
% 0.99/1.17          | ~ (v1_xboole_0 @ X14)
% 0.99/1.17          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t5_subset])).
% 0.99/1.17  thf('67', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['65', '66'])).
% 0.99/1.17  thf('68', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.99/1.17      inference('sup-', [status(thm)], ['64', '67'])).
% 0.99/1.17  thf('69', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.99/1.17      inference('sup-', [status(thm)], ['63', '68'])).
% 0.99/1.17  thf(d10_xboole_0, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.17  thf('70', plain,
% 0.99/1.17      (![X4 : $i, X6 : $i]:
% 0.99/1.17         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.99/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.17  thf('71', plain,
% 0.99/1.17      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['69', '70'])).
% 0.99/1.17  thf('72', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['62', '71'])).
% 0.99/1.17  thf('73', plain,
% 0.99/1.17      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.17  thf(fc9_tops_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]:
% 0.99/1.17     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.99/1.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.17       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.99/1.17  thf('74', plain,
% 0.99/1.17      (![X18 : $i, X19 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X18)
% 0.99/1.17          | ~ (v2_pre_topc @ X18)
% 0.99/1.17          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.99/1.17          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 0.99/1.17      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.99/1.17  thf('75', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v3_pre_topc @ (k1_tops_1 @ X0 @ k1_xboole_0) @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['73', '74'])).
% 0.99/1.17  thf('76', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['72', '75'])).
% 0.99/1.17  thf('77', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.99/1.17      inference('simplify', [status(thm)], ['76'])).
% 0.99/1.17  thf('78', plain,
% 0.99/1.17      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.17  thf('79', plain,
% 0.99/1.17      (![X16 : $i, X17 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.99/1.17          | ~ (v3_pre_topc @ X16 @ X17)
% 0.99/1.17          | (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.99/1.17          | ~ (l1_pre_topc @ X17))),
% 0.99/1.17      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.99/1.17  thf('80', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | (r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X0))
% 0.99/1.17          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['78', '79'])).
% 0.99/1.17  thf('81', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X0))
% 0.99/1.17          | ~ (l1_pre_topc @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['77', '80'])).
% 0.99/1.17  thf('82', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X0))
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0))),
% 0.99/1.17      inference('simplify', [status(thm)], ['81'])).
% 0.99/1.17  thf('83', plain,
% 0.99/1.17      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.17  thf('84', plain,
% 0.99/1.17      (![X24 : $i, X25 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.99/1.17          | ~ (r2_hidden @ X24 @ (u1_pre_topc @ X25))
% 0.99/1.17          | ((u1_pre_topc @ X25) = (k5_tmap_1 @ X25 @ X24))
% 0.99/1.17          | ~ (l1_pre_topc @ X25)
% 0.99/1.17          | ~ (v2_pre_topc @ X25)
% 0.99/1.17          | (v2_struct_0 @ X25))),
% 0.99/1.17      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.99/1.17  thf('85', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17          | ~ (r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['83', '84'])).
% 0.99/1.17  thf('86', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (v2_struct_0 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['82', '85'])).
% 0.99/1.17  thf('87', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v2_struct_0 @ X0)
% 0.99/1.17          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0))),
% 0.99/1.17      inference('simplify', [status(thm)], ['86'])).
% 0.99/1.17  thf('88', plain,
% 0.99/1.17      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.17  thf('89', plain,
% 0.99/1.17      (![X26 : $i, X27 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.17          | ((u1_pre_topc @ (k6_tmap_1 @ X27 @ X26)) = (k5_tmap_1 @ X27 @ X26))
% 0.99/1.17          | ~ (l1_pre_topc @ X27)
% 0.99/1.17          | ~ (v2_pre_topc @ X27)
% 0.99/1.17          | (v2_struct_0 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.99/1.17  thf('90', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17              = (k5_tmap_1 @ X0 @ k1_xboole_0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['88', '89'])).
% 0.99/1.17  thf('91', plain,
% 0.99/1.17      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17          = (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('split', [status(esa)], ['2'])).
% 0.99/1.17  thf('92', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v2_struct_0 @ X0)
% 0.99/1.17          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0))),
% 0.99/1.17      inference('simplify', [status(thm)], ['86'])).
% 0.99/1.17  thf('93', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17              = (k5_tmap_1 @ X0 @ k1_xboole_0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['88', '89'])).
% 0.99/1.17  thf('94', plain,
% 0.99/1.17      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.17  thf('95', plain,
% 0.99/1.17      (![X22 : $i, X23 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X22)
% 0.99/1.17          | ~ (v2_pre_topc @ X22)
% 0.99/1.17          | (v2_struct_0 @ X22)
% 0.99/1.17          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.99/1.17          | (v1_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.99/1.17  thf('96', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['94', '95'])).
% 0.99/1.17  thf('97', plain,
% 0.99/1.17      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.17  thf('98', plain,
% 0.99/1.17      (![X22 : $i, X23 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X22)
% 0.99/1.17          | ~ (v2_pre_topc @ X22)
% 0.99/1.17          | (v2_struct_0 @ X22)
% 0.99/1.17          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.99/1.17          | (l1_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.99/1.17  thf('99', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((l1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['97', '98'])).
% 0.99/1.17  thf('100', plain,
% 0.99/1.17      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.17  thf('101', plain,
% 0.99/1.17      (![X26 : $i, X27 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.17          | ((u1_struct_0 @ (k6_tmap_1 @ X27 @ X26)) = (u1_struct_0 @ X27))
% 0.99/1.17          | ~ (l1_pre_topc @ X27)
% 0.99/1.17          | ~ (v2_pre_topc @ X27)
% 0.99/1.17          | (v2_struct_0 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.99/1.17  thf('102', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ((u1_struct_0 @ (k6_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17              = (u1_struct_0 @ X0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['100', '101'])).
% 0.99/1.17  thf('103', plain,
% 0.99/1.17      (![X15 : $i]:
% 0.99/1.17         (~ (v1_pre_topc @ X15)
% 0.99/1.17          | ((X15) = (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.99/1.17          | ~ (l1_pre_topc @ X15))),
% 0.99/1.17      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.99/1.17  thf('104', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k6_tmap_1 @ X0 @ k1_xboole_0)
% 0.99/1.17            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.99/1.17               (u1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))))
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0)))),
% 0.99/1.17      inference('sup+', [status(thm)], ['102', '103'])).
% 0.99/1.17  thf('105', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ((k6_tmap_1 @ X0 @ k1_xboole_0)
% 0.99/1.17              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.99/1.17                 (u1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0)))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['99', '104'])).
% 0.99/1.17  thf('106', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k6_tmap_1 @ X0 @ k1_xboole_0)
% 0.99/1.17            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.99/1.17               (u1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))))
% 0.99/1.17          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0))),
% 0.99/1.17      inference('simplify', [status(thm)], ['105'])).
% 0.99/1.17  thf('107', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ((k6_tmap_1 @ X0 @ k1_xboole_0)
% 0.99/1.17              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.99/1.17                 (u1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0)))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['96', '106'])).
% 0.99/1.17  thf('108', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k6_tmap_1 @ X0 @ k1_xboole_0)
% 0.99/1.17            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.99/1.17               (u1_pre_topc @ (k6_tmap_1 @ X0 @ k1_xboole_0))))
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0))),
% 0.99/1.17      inference('simplify', [status(thm)], ['107'])).
% 0.99/1.17  thf('109', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k6_tmap_1 @ X0 @ k1_xboole_0)
% 0.99/1.17            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.99/1.17               (k5_tmap_1 @ X0 @ k1_xboole_0)))
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (v2_struct_0 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['93', '108'])).
% 0.99/1.17  thf('110', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ((k6_tmap_1 @ X0 @ k1_xboole_0)
% 0.99/1.17              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.99/1.17                 (k5_tmap_1 @ X0 @ k1_xboole_0))))),
% 0.99/1.17      inference('simplify', [status(thm)], ['109'])).
% 0.99/1.17  thf('111', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k6_tmap_1 @ X0 @ k1_xboole_0)
% 0.99/1.17            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (v2_struct_0 @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | (v2_struct_0 @ X0))),
% 0.99/1.17      inference('sup+', [status(thm)], ['92', '110'])).
% 0.99/1.17  thf('112', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         ((v2_struct_0 @ X0)
% 0.99/1.17          | ~ (v2_pre_topc @ X0)
% 0.99/1.17          | ~ (l1_pre_topc @ X0)
% 0.99/1.17          | ((k6_tmap_1 @ X0 @ k1_xboole_0)
% 0.99/1.17              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.99/1.17      inference('simplify', [status(thm)], ['111'])).
% 0.99/1.17  thf('113', plain,
% 0.99/1.17      (((((k6_tmap_1 @ sk_A @ k1_xboole_0) = (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17         | ~ (l1_pre_topc @ sk_A)
% 0.99/1.17         | ~ (v2_pre_topc @ sk_A)
% 0.99/1.17         | (v2_struct_0 @ sk_A)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('sup+', [status(thm)], ['91', '112'])).
% 0.99/1.17  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('116', plain,
% 0.99/1.17      (((((k6_tmap_1 @ sk_A @ k1_xboole_0) = (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17         | (v2_struct_0 @ sk_A)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.99/1.17  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('118', plain,
% 0.99/1.17      ((((k6_tmap_1 @ sk_A @ k1_xboole_0) = (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('clc', [status(thm)], ['116', '117'])).
% 0.99/1.17  thf('119', plain,
% 0.99/1.17      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17         = (k5_tmap_1 @ sk_A @ sk_B_1))),
% 0.99/1.17      inference('clc', [status(thm)], ['51', '52'])).
% 0.99/1.17  thf('120', plain,
% 0.99/1.17      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ k1_xboole_0))
% 0.99/1.17          = (k5_tmap_1 @ sk_A @ sk_B_1)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('sup+', [status(thm)], ['118', '119'])).
% 0.99/1.17  thf('121', plain,
% 0.99/1.17      (((((k5_tmap_1 @ sk_A @ k1_xboole_0) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17         | ~ (l1_pre_topc @ sk_A)
% 0.99/1.17         | ~ (v2_pre_topc @ sk_A)
% 0.99/1.17         | (v2_struct_0 @ sk_A)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('sup+', [status(thm)], ['90', '120'])).
% 0.99/1.17  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('124', plain,
% 0.99/1.17      (((((k5_tmap_1 @ sk_A @ k1_xboole_0) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17         | (v2_struct_0 @ sk_A)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.99/1.17  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('126', plain,
% 0.99/1.17      ((((k5_tmap_1 @ sk_A @ k1_xboole_0) = (k5_tmap_1 @ sk_A @ sk_B_1)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('clc', [status(thm)], ['124', '125'])).
% 0.99/1.17  thf('127', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('128', plain,
% 0.99/1.17      (![X24 : $i, X25 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.99/1.17          | ((u1_pre_topc @ X25) != (k5_tmap_1 @ X25 @ X24))
% 0.99/1.17          | (r2_hidden @ X24 @ (u1_pre_topc @ X25))
% 0.99/1.17          | ~ (l1_pre_topc @ X25)
% 0.99/1.17          | ~ (v2_pre_topc @ X25)
% 0.99/1.17          | (v2_struct_0 @ X25))),
% 0.99/1.17      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.99/1.17  thf('129', plain,
% 0.99/1.17      (((v2_struct_0 @ sk_A)
% 0.99/1.17        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.17        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['127', '128'])).
% 0.99/1.17  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('132', plain,
% 0.99/1.17      (((v2_struct_0 @ sk_A)
% 0.99/1.17        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.99/1.17        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.99/1.17      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.99/1.17  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('134', plain,
% 0.99/1.17      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.99/1.17        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.99/1.17      inference('clc', [status(thm)], ['132', '133'])).
% 0.99/1.17  thf('135', plain,
% 0.99/1.17      (((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ k1_xboole_0))
% 0.99/1.17         | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['126', '134'])).
% 0.99/1.17  thf('136', plain,
% 0.99/1.17      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.99/1.17         | ~ (l1_pre_topc @ sk_A)
% 0.99/1.17         | ~ (v2_pre_topc @ sk_A)
% 0.99/1.17         | (v2_struct_0 @ sk_A)
% 0.99/1.17         | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['87', '135'])).
% 0.99/1.17  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('138', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('139', plain,
% 0.99/1.17      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.99/1.17         | (v2_struct_0 @ sk_A)
% 0.99/1.17         | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.99/1.17  thf('140', plain,
% 0.99/1.17      ((((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('simplify', [status(thm)], ['139'])).
% 0.99/1.17  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('142', plain,
% 0.99/1.17      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('clc', [status(thm)], ['140', '141'])).
% 0.99/1.17  thf('143', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('144', plain,
% 0.99/1.17      (![X16 : $i, X17 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.99/1.17          | ~ (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 0.99/1.17          | (v3_pre_topc @ X16 @ X17)
% 0.99/1.17          | ~ (l1_pre_topc @ X17))),
% 0.99/1.17      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.99/1.17  thf('145', plain,
% 0.99/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.17        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.99/1.17        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['143', '144'])).
% 0.99/1.17  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('147', plain,
% 0.99/1.17      (((v3_pre_topc @ sk_B_1 @ sk_A)
% 0.99/1.17        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['145', '146'])).
% 0.99/1.17  thf('148', plain,
% 0.99/1.17      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 0.99/1.17         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['142', '147'])).
% 0.99/1.17  thf('149', plain,
% 0.99/1.17      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.99/1.17      inference('split', [status(esa)], ['0'])).
% 0.99/1.17  thf('150', plain,
% 0.99/1.17      (~
% 0.99/1.17       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.17          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.99/1.17       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['148', '149'])).
% 0.99/1.17  thf('151', plain, ($false),
% 0.99/1.17      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '150'])).
% 0.99/1.17  
% 0.99/1.17  % SZS output end Refutation
% 0.99/1.17  
% 0.99/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
