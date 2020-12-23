%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OWhsCso8f5

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 223 expanded)
%              Number of leaves         :   21 (  70 expanded)
%              Depth                    :   23
%              Number of atoms          : 1257 (3275 expanded)
%              Number of equality atoms :   72 ( 154 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X5 @ ( u1_pre_topc @ X6 ) )
      | ( ( u1_pre_topc @ X6 )
        = ( k5_tmap_1 @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( ( k6_tmap_1 @ X4 @ X3 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( k5_tmap_1 @ X4 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf('28',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ( k6_tmap_1 @ sk_A @ sk_B_1 )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(rc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_pre_topc @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X2: $i] :
      ( ( v3_pre_topc @ ( sk_B @ X2 ) @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc1_tops_1])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc1_tops_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc1_tops_1])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X5 @ ( u1_pre_topc @ X6 ) )
      | ( ( u1_pre_topc @ X6 )
        = ( k5_tmap_1 @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc1_tops_1])).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( ( k6_tmap_1 @ X4 @ X3 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( k5_tmap_1 @ X4 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
        = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
        = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( sk_B @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc1_tops_1])).

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

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X8 @ X7 ) )
        = ( k5_tmap_1 @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
        = ( k5_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X8 @ X7 ) )
        = ( k5_tmap_1 @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( k5_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B_1 )
        = ( k5_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['63','71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B_1 )
      = ( k5_tmap_1 @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B_1 )
        = ( u1_pre_topc @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['44','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B_1 )
        = ( u1_pre_topc @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B_1 )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( u1_pre_topc @ X6 )
       != ( k5_tmap_1 @ X6 @ X5 ) )
      | ( r2_hidden @ X5 @ ( u1_pre_topc @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,
    ( ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OWhsCso8f5
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:32:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 77 iterations in 0.046s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(t106_tmap_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.49             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.49               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49              ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.49                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.49                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          != (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.49       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d5_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.49             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.49          | ~ (v3_pre_topc @ X0 @ X1)
% 0.20/0.49          | (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.20/0.49          | ~ (l1_pre_topc @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))
% 0.20/0.49         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t103_tmap_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.20/0.49             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.49          | ~ (r2_hidden @ X5 @ (u1_pre_topc @ X6))
% 0.20/0.49          | ((u1_pre_topc @ X6) = (k5_tmap_1 @ X6 @ X5))
% 0.20/0.49          | ~ (l1_pre_topc @ X6)
% 0.20/0.49          | ~ (v2_pre_topc @ X6)
% 0.20/0.49          | (v2_struct_0 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.49  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B_1)))
% 0.20/0.49         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d9_tmap_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( k6_tmap_1 @ A @ B ) =
% 0.20/0.49             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.49          | ((k6_tmap_1 @ X4 @ X3)
% 0.20/0.49              = (g1_pre_topc @ (u1_struct_0 @ X4) @ (k5_tmap_1 @ X4 @ X3)))
% 0.20/0.49          | ~ (l1_pre_topc @ X4)
% 0.20/0.49          | ~ (v2_pre_topc @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.20/0.49            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.20/0.49            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.49  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.20/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.20/0.49      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((((k6_tmap_1 @ sk_A @ sk_B_1)
% 0.20/0.49          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.49         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['18', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          != (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((k6_tmap_1 @ sk_A @ sk_B_1) != (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.49             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.49       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.49       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf(rc1_tops_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ?[B:$i]:
% 0.20/0.49         ( ( v3_pre_topc @ B @ A ) & 
% 0.20/0.49           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         ((v3_pre_topc @ (sk_B @ X2) @ X2)
% 0.20/0.49          | ~ (l1_pre_topc @ X2)
% 0.20/0.49          | ~ (v2_pre_topc @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [rc1_tops_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.49          | ~ (l1_pre_topc @ X2)
% 0.20/0.49          | ~ (v2_pre_topc @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [rc1_tops_1])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.49          | ~ (v3_pre_topc @ X0 @ X1)
% 0.20/0.49          | (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.20/0.49          | ~ (l1_pre_topc @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.49          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.20/0.49          | (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.49          | ~ (l1_pre_topc @ X2)
% 0.20/0.49          | ~ (v2_pre_topc @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [rc1_tops_1])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.49          | ~ (r2_hidden @ X5 @ (u1_pre_topc @ X6))
% 0.20/0.49          | ((u1_pre_topc @ X6) = (k5_tmap_1 @ X6 @ X5))
% 0.20/0.49          | ~ (l1_pre_topc @ X6)
% 0.20/0.49          | ~ (v2_pre_topc @ X6)
% 0.20/0.49          | (v2_struct_0 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.20/0.49          | ~ (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (sk_B @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.49          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.49          | ~ (l1_pre_topc @ X2)
% 0.20/0.49          | ~ (v2_pre_topc @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [rc1_tops_1])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.49          | ((k6_tmap_1 @ X4 @ X3)
% 0.20/0.49              = (g1_pre_topc @ (u1_struct_0 @ X4) @ (k5_tmap_1 @ X4 @ X3)))
% 0.20/0.49          | ~ (l1_pre_topc @ X4)
% 0.20/0.49          | ~ (v2_pre_topc @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.20/0.49              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.20/0.49                 (k5_tmap_1 @ X0 @ (sk_B @ X0)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.20/0.49            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.20/0.49               (k5_tmap_1 @ X0 @ (sk_B @ X0))))
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.20/0.49            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['46', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ((k6_tmap_1 @ X0 @ (sk_B @ X0))
% 0.20/0.49              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A)) = (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['45', '52'])).
% 0.20/0.49  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A)) = (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49         | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.49  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      ((((k6_tmap_1 @ sk_A @ (sk_B @ sk_A)) = (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X2 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.49          | ~ (l1_pre_topc @ X2)
% 0.20/0.49          | ~ (v2_pre_topc @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [rc1_tops_1])).
% 0.20/0.49  thf(t104_tmap_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.49             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.49          | ((u1_pre_topc @ (k6_tmap_1 @ X8 @ X7)) = (k5_tmap_1 @ X8 @ X7))
% 0.20/0.49          | ~ (l1_pre_topc @ X8)
% 0.20/0.49          | ~ (v2_pre_topc @ X8)
% 0.20/0.49          | (v2_struct_0 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.20/0.49              = (k5_tmap_1 @ X0 @ (sk_B @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((u1_pre_topc @ (k6_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.20/0.49            = (k5_tmap_1 @ X0 @ (sk_B @ X0)))
% 0.20/0.49          | (v2_struct_0 @ X0)
% 0.20/0.49          | ~ (l1_pre_topc @ X0)
% 0.20/0.49          | ~ (v2_pre_topc @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49           = (k5_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.20/0.49         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['58', '62'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.49          | ((u1_pre_topc @ (k6_tmap_1 @ X8 @ X7)) = (k5_tmap_1 @ X8 @ X7))
% 0.20/0.49          | ~ (l1_pre_topc @ X8)
% 0.20/0.49          | ~ (v2_pre_topc @ X8)
% 0.20/0.49          | (v2_struct_0 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49            = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.49  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49            = (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.20/0.49  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49         = (k5_tmap_1 @ sk_A @ sk_B_1))),
% 0.20/0.49      inference('clc', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      (((((k5_tmap_1 @ sk_A @ sk_B_1) = (k5_tmap_1 @ sk_A @ (sk_B @ sk_A)))
% 0.20/0.49         | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('demod', [status(thm)], ['63', '71', '72', '73'])).
% 0.20/0.49  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      ((((k5_tmap_1 @ sk_A @ sk_B_1) = (k5_tmap_1 @ sk_A @ (sk_B @ sk_A))))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      (((((k5_tmap_1 @ sk_A @ sk_B_1) = (u1_pre_topc @ sk_A))
% 0.20/0.49         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49         | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['44', '76'])).
% 0.20/0.49  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (((((k5_tmap_1 @ sk_A @ sk_B_1) = (u1_pre_topc @ sk_A))
% 0.20/0.49         | (v2_struct_0 @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.20/0.49  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('82', plain,
% 0.20/0.49      ((((k5_tmap_1 @ sk_A @ sk_B_1) = (u1_pre_topc @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.49          | ((u1_pre_topc @ X6) != (k5_tmap_1 @ X6 @ X5))
% 0.20/0.49          | (r2_hidden @ X5 @ (u1_pre_topc @ X6))
% 0.20/0.49          | ~ (l1_pre_topc @ X6)
% 0.20/0.49          | ~ (v2_pre_topc @ X6)
% 0.20/0.49          | (v2_struct_0 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.20/0.49  thf('85', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.49  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('88', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A)
% 0.20/0.49        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))
% 0.20/0.49        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.20/0.49  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('90', plain,
% 0.20/0.49      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B_1))
% 0.20/0.49        | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['88', '89'])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.20/0.49         | (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A))))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['82', '90'])).
% 0.20/0.49  thf('92', plain,
% 0.20/0.49      (((r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['91'])).
% 0.20/0.49  thf('93', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.20/0.49          | (v3_pre_topc @ X0 @ X1)
% 0.20/0.49          | ~ (l1_pre_topc @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.49  thf('95', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.49        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.49        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.49  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('97', plain,
% 0.20/0.49      (((v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.49        | ~ (r2_hidden @ sk_B_1 @ (u1_pre_topc @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.49  thf('98', plain,
% 0.20/0.49      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 0.20/0.49         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49                = (k6_tmap_1 @ sk_A @ sk_B_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['92', '97'])).
% 0.20/0.49  thf('99', plain,
% 0.20/0.49      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('100', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.49          = (k6_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.49       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.49  thf('101', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '100'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
