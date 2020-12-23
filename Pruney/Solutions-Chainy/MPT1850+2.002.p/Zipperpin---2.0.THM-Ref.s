%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yaYXkLwH2w

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:58 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  241 (4264 expanded)
%              Number of leaves         :   36 (1247 expanded)
%              Depth                    :   27
%              Number of atoms          : 1934 (48656 expanded)
%              Number of equality atoms :   61 (1678 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t17_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v1_tdlat_3 @ A ) )
           => ( v1_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v1_tdlat_3 @ A ) )
             => ( v1_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tex_2])).

thf('0',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('3',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( X27
       != ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) )
      | ~ ( m1_pre_topc @ X27 @ X29 )
      | ( m1_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('11',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) @ X29 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('21',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('29',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t58_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
       => ( v2_pre_topc @ A ) ) ) )).

thf('30',plain,(
    ! [X13: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X13 ) @ ( u1_pre_topc @ X13 ) ) )
      | ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t58_pre_topc])).

thf('31',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('36',plain,(
    ! [X37: $i] :
      ( ~ ( v1_tdlat_3 @ X37 )
      | ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('37',plain,
    ( ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','27','41','42','43'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X30: $i] :
      ( ( m1_pre_topc @ X30 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X33 )
      | ( r1_tarski @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','39','40'])).

thf('56',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('57',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('58',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) @ X29 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ X0 )
      | ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X12: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('62',plain,
    ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['34','39','40'])).

thf('66',plain,(
    v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ X0 )
      | ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['59','66','67','68'])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','72'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['70','71'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('81',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('83',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','83'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('85',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('86',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('87',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('88',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k9_setfam_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('89',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_tops_2 @ X23 @ X24 )
      | ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('90',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('91',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('92',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_tops_2 @ X23 @ X24 )
      | ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','92'])).

thf('94',plain,
    ( ~ ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r1_tarski @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_B ) ) @ ( u1_pre_topc @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','83'])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r1_tarski @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf(d1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('98',plain,(
    ! [X38: $i] :
      ( ~ ( v1_tdlat_3 @ X38 )
      | ( ( u1_pre_topc @ X38 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('99',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k9_setfam_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('100',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ( v1_tops_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('101',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('102',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('103',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ( v1_tops_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( r1_tarski @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('107',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','92'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( r1_tarski @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ X0 )
      | ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['59','66','67','68'])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_pre_topc @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['115','116','117'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('119',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('120',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('121',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('122',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf(t31_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('123',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_2])).

thf('124',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('125',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('126',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('127',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('128',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','128'])).

thf('130',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['118','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('134',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('135',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('136',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k9_setfam_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('139',plain,
    ( ~ ( r1_tarski @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,
    ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('145',plain,
    ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','143','144'])).

thf('146',plain,(
    ! [X38: $i] :
      ( ~ ( v1_tdlat_3 @ X38 )
      | ( ( u1_pre_topc @ X38 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('147',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','83'])).

thf('148',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('149',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k9_setfam_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['147','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['146','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('159',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X38: $i] :
      ( ~ ( v1_tdlat_3 @ X38 )
      | ( ( u1_pre_topc @ X38 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('161',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','83'])).

thf('162',plain,(
    ! [X38: $i] :
      ( ( ( u1_pre_topc @ X38 )
       != ( k9_setfam_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( v1_tdlat_3 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('163',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v1_tdlat_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ( u1_pre_topc @ sk_B )
 != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','167'])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ( u1_pre_topc @ sk_B )
 != ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['159','171'])).

thf('173',plain,(
    ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['145','172'])).

thf('174',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('175',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','83'])).

thf('176',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k9_setfam_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf(t35_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v1_tops_2 @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                   => ( ( D = B )
                     => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) )).

thf('177',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ( v1_tops_2 @ X21 @ X22 )
      | ( X21 != X19 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('178',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v1_tops_2 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('180',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('181',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('182',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('183',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v1_tops_2 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X19 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_tops_2 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ X1 )
      | ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['176','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_B ) ) @ sk_B )
      | ~ ( v1_tops_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','184'])).

thf('186',plain,
    ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('187',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','83'])).

thf('188',plain,
    ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('189',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','83'])).

thf('190',plain,
    ( ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['185','186','187','188','189','190'])).

thf('192',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['174','191'])).

thf('193',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('195',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( r1_tarski @ X23 @ ( u1_pre_topc @ X24 ) )
      | ( v1_tops_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('196',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('199',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['192','193','199','200','201'])).

thf('203',plain,(
    $false ),
    inference(demod,[status(thm)],['173','202'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yaYXkLwH2w
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.32  % CPULimit   : 60
% 0.18/0.32  % DateTime   : Tue Dec  1 15:10:09 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.33  % Running portfolio for 600 s
% 0.18/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.18/0.33  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.33  % Running in FO mode
% 0.85/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.06  % Solved by: fo/fo7.sh
% 0.85/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.06  % done 803 iterations in 0.617s
% 0.85/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.06  % SZS output start Refutation
% 0.85/1.06  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.85/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.06  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.85/1.06  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.85/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.85/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.85/1.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.85/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.85/1.06  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.85/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.06  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.85/1.06  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.85/1.06  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.85/1.06  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.85/1.06  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.85/1.06  thf(t17_tex_2, conjecture,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ![B:$i]:
% 0.85/1.06         ( ( l1_pre_topc @ B ) =>
% 0.85/1.06           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.85/1.06                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.85/1.06               ( v1_tdlat_3 @ A ) ) =>
% 0.85/1.06             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.85/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.06    (~( ![A:$i]:
% 0.85/1.06        ( ( l1_pre_topc @ A ) =>
% 0.85/1.06          ( ![B:$i]:
% 0.85/1.06            ( ( l1_pre_topc @ B ) =>
% 0.85/1.06              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.85/1.06                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.85/1.06                  ( v1_tdlat_3 @ A ) ) =>
% 0.85/1.06                ( v1_tdlat_3 @ B ) ) ) ) ) )),
% 0.85/1.06    inference('cnf.neg', [status(esa)], [t17_tex_2])).
% 0.85/1.06  thf('0', plain,
% 0.85/1.06      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.85/1.06         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf(t2_tsep_1, axiom,
% 0.85/1.06    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.85/1.06  thf('1', plain,
% 0.85/1.06      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 0.85/1.06      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.85/1.06  thf(fc6_pre_topc, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.85/1.06       ( ( v1_pre_topc @
% 0.85/1.06           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.85/1.06         ( v2_pre_topc @
% 0.85/1.06           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.85/1.06  thf('2', plain,
% 0.85/1.06      (![X12 : $i]:
% 0.85/1.06         ((v2_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.85/1.06          | ~ (l1_pre_topc @ X12)
% 0.85/1.06          | ~ (v2_pre_topc @ X12))),
% 0.85/1.06      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.85/1.06  thf('3', plain,
% 0.85/1.06      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 0.85/1.06      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.85/1.06  thf(t11_tmap_1, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ![B:$i]:
% 0.85/1.06         ( ( m1_pre_topc @ B @ A ) =>
% 0.85/1.06           ( ( v1_pre_topc @
% 0.85/1.06               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.85/1.06             ( m1_pre_topc @
% 0.85/1.06               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.85/1.06  thf('4', plain,
% 0.85/1.06      (![X25 : $i, X26 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ X25 @ X26)
% 0.85/1.06          | (m1_pre_topc @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)) @ X26)
% 0.85/1.06          | ~ (l1_pre_topc @ X26))),
% 0.85/1.06      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.85/1.06  thf('5', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | (m1_pre_topc @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['3', '4'])).
% 0.85/1.06  thf('6', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         ((m1_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['5'])).
% 0.85/1.06  thf(dt_m1_pre_topc, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.85/1.06  thf('7', plain,
% 0.85/1.06      (![X9 : $i, X10 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ X9 @ X10)
% 0.85/1.06          | (l1_pre_topc @ X9)
% 0.85/1.06          | ~ (l1_pre_topc @ X10))),
% 0.85/1.06      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.85/1.06  thf('8', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | (l1_pre_topc @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.85/1.06      inference('sup-', [status(thm)], ['6', '7'])).
% 0.85/1.06  thf('9', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         ((l1_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['8'])).
% 0.85/1.06  thf(t12_tmap_1, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ![B:$i]:
% 0.85/1.06         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.85/1.06           ( ![C:$i]:
% 0.85/1.06             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.85/1.06               ( ( ( B ) =
% 0.85/1.06                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.85/1.06                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.85/1.06  thf('10', plain,
% 0.85/1.06      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.85/1.06         (~ (v2_pre_topc @ X27)
% 0.85/1.06          | ~ (l1_pre_topc @ X27)
% 0.85/1.06          | ((X27) != (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)))
% 0.85/1.06          | ~ (m1_pre_topc @ X27 @ X29)
% 0.85/1.06          | (m1_pre_topc @ X28 @ X29)
% 0.85/1.06          | ~ (l1_pre_topc @ X28)
% 0.85/1.06          | ~ (v2_pre_topc @ X28)
% 0.85/1.06          | ~ (l1_pre_topc @ X29))),
% 0.85/1.06      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.85/1.06  thf('11', plain,
% 0.85/1.06      (![X28 : $i, X29 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X29)
% 0.85/1.06          | ~ (v2_pre_topc @ X28)
% 0.85/1.06          | ~ (l1_pre_topc @ X28)
% 0.85/1.06          | (m1_pre_topc @ X28 @ X29)
% 0.85/1.06          | ~ (m1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)) @ X29)
% 0.85/1.06          | ~ (l1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)))
% 0.85/1.06          | ~ (v2_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28))))),
% 0.85/1.06      inference('simplify', [status(thm)], ['10'])).
% 0.85/1.06  thf('12', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (v2_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.85/1.06          | ~ (m1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.85/1.06          | (m1_pre_topc @ X0 @ X1)
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (v2_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['9', '11'])).
% 0.85/1.06  thf('13', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X1)
% 0.85/1.06          | ~ (v2_pre_topc @ X0)
% 0.85/1.06          | (m1_pre_topc @ X0 @ X1)
% 0.85/1.06          | ~ (m1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.85/1.06          | ~ (v2_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['12'])).
% 0.85/1.06  thf('14', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (v2_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (m1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.85/1.06          | (m1_pre_topc @ X0 @ X1)
% 0.85/1.06          | ~ (v2_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['2', '13'])).
% 0.85/1.06  thf('15', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X1)
% 0.85/1.06          | (m1_pre_topc @ X0 @ X1)
% 0.85/1.06          | ~ (m1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (v2_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['14'])).
% 0.85/1.06  thf('16', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.85/1.06          | ~ (v2_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | (m1_pre_topc @ X0 @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.85/1.06          | ~ (l1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.85/1.06      inference('sup-', [status(thm)], ['1', '15'])).
% 0.85/1.06  thf('17', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         ((m1_pre_topc @ X0 @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (v2_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.85/1.06      inference('simplify', [status(thm)], ['16'])).
% 0.85/1.06  thf('18', plain,
% 0.85/1.06      ((~ (l1_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.85/1.06        | ~ (v2_pre_topc @ sk_B)
% 0.85/1.06        | ~ (l1_pre_topc @ sk_B)
% 0.85/1.06        | (m1_pre_topc @ sk_B @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.85/1.06      inference('sup-', [status(thm)], ['0', '17'])).
% 0.85/1.06  thf('19', plain,
% 0.85/1.06      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.85/1.06         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('20', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         ((m1_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['5'])).
% 0.85/1.06  thf('21', plain,
% 0.85/1.06      (((m1_pre_topc @ 
% 0.85/1.06         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.85/1.06        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.06      inference('sup+', [status(thm)], ['19', '20'])).
% 0.85/1.06  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('23', plain,
% 0.85/1.06      ((m1_pre_topc @ 
% 0.85/1.06        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)),
% 0.85/1.06      inference('demod', [status(thm)], ['21', '22'])).
% 0.85/1.06  thf('24', plain,
% 0.85/1.06      (![X9 : $i, X10 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ X9 @ X10)
% 0.85/1.06          | (l1_pre_topc @ X9)
% 0.85/1.06          | ~ (l1_pre_topc @ X10))),
% 0.85/1.06      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.85/1.06  thf('25', plain,
% 0.85/1.06      ((~ (l1_pre_topc @ sk_B)
% 0.85/1.06        | (l1_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.85/1.06      inference('sup-', [status(thm)], ['23', '24'])).
% 0.85/1.06  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('27', plain,
% 0.85/1.06      ((l1_pre_topc @ 
% 0.85/1.06        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.85/1.06      inference('demod', [status(thm)], ['25', '26'])).
% 0.85/1.06  thf('28', plain,
% 0.85/1.06      (![X12 : $i]:
% 0.85/1.06         ((v2_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.85/1.06          | ~ (l1_pre_topc @ X12)
% 0.85/1.06          | ~ (v2_pre_topc @ X12))),
% 0.85/1.06      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.85/1.06  thf('29', plain,
% 0.85/1.06      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.85/1.06         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf(t58_pre_topc, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ( v2_pre_topc @
% 0.85/1.06           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.85/1.06         ( v2_pre_topc @ A ) ) ))).
% 0.85/1.06  thf('30', plain,
% 0.85/1.06      (![X13 : $i]:
% 0.85/1.06         (~ (v2_pre_topc @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ X13) @ (u1_pre_topc @ X13)))
% 0.85/1.06          | (v2_pre_topc @ X13)
% 0.85/1.06          | ~ (l1_pre_topc @ X13))),
% 0.85/1.06      inference('cnf', [status(esa)], [t58_pre_topc])).
% 0.85/1.06  thf('31', plain,
% 0.85/1.06      ((~ (v2_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.85/1.06        | ~ (l1_pre_topc @ sk_B)
% 0.85/1.06        | (v2_pre_topc @ sk_B))),
% 0.85/1.06      inference('sup-', [status(thm)], ['29', '30'])).
% 0.85/1.06  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('33', plain,
% 0.85/1.06      ((~ (v2_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.85/1.06        | (v2_pre_topc @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['31', '32'])).
% 0.85/1.06  thf('34', plain,
% 0.85/1.06      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.85/1.06      inference('sup-', [status(thm)], ['28', '33'])).
% 0.85/1.06  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf(cc1_tdlat_3, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) => ( ( v1_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.85/1.06  thf('36', plain,
% 0.85/1.06      (![X37 : $i]:
% 0.85/1.06         (~ (v1_tdlat_3 @ X37) | (v2_pre_topc @ X37) | ~ (l1_pre_topc @ X37))),
% 0.85/1.06      inference('cnf', [status(esa)], [cc1_tdlat_3])).
% 0.85/1.06  thf('37', plain, (((v2_pre_topc @ sk_A) | ~ (v1_tdlat_3 @ sk_A))),
% 0.85/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.85/1.06  thf('38', plain, ((v1_tdlat_3 @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.85/1.06      inference('demod', [status(thm)], ['37', '38'])).
% 0.85/1.06  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.85/1.06      inference('demod', [status(thm)], ['34', '39', '40'])).
% 0.85/1.06  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('43', plain,
% 0.85/1.06      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.85/1.06         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('44', plain,
% 0.85/1.06      ((m1_pre_topc @ sk_B @ 
% 0.85/1.06        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.85/1.06      inference('demod', [status(thm)], ['18', '27', '41', '42', '43'])).
% 0.85/1.06  thf(t59_pre_topc, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ![B:$i]:
% 0.85/1.06         ( ( m1_pre_topc @
% 0.85/1.06             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.85/1.06           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.85/1.06  thf('45', plain,
% 0.85/1.06      (![X14 : $i, X15 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ X14 @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.85/1.06          | (m1_pre_topc @ X14 @ X15)
% 0.85/1.06          | ~ (l1_pre_topc @ X15))),
% 0.85/1.06      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.85/1.06  thf('46', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.85/1.06      inference('sup-', [status(thm)], ['44', '45'])).
% 0.85/1.06  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('48', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.85/1.06      inference('demod', [status(thm)], ['46', '47'])).
% 0.85/1.06  thf('49', plain,
% 0.85/1.06      (![X30 : $i]: ((m1_pre_topc @ X30 @ X30) | ~ (l1_pre_topc @ X30))),
% 0.85/1.06      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.85/1.06  thf(t4_tsep_1, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.85/1.06       ( ![B:$i]:
% 0.85/1.06         ( ( m1_pre_topc @ B @ A ) =>
% 0.85/1.06           ( ![C:$i]:
% 0.85/1.06             ( ( m1_pre_topc @ C @ A ) =>
% 0.85/1.06               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.85/1.06                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.85/1.06  thf('50', plain,
% 0.85/1.06      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ X31 @ X32)
% 0.85/1.06          | ~ (m1_pre_topc @ X31 @ X33)
% 0.85/1.06          | (r1_tarski @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X33))
% 0.85/1.06          | ~ (m1_pre_topc @ X33 @ X32)
% 0.85/1.06          | ~ (l1_pre_topc @ X32)
% 0.85/1.06          | ~ (v2_pre_topc @ X32))),
% 0.85/1.06      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.85/1.06  thf('51', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (v2_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (m1_pre_topc @ X1 @ X0)
% 0.85/1.06          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.85/1.06          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['49', '50'])).
% 0.85/1.06  thf('52', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ X0 @ X1)
% 0.85/1.06          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.85/1.06          | ~ (m1_pre_topc @ X1 @ X0)
% 0.85/1.06          | ~ (v2_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['51'])).
% 0.85/1.06  thf('53', plain,
% 0.85/1.06      ((~ (l1_pre_topc @ sk_B)
% 0.85/1.06        | ~ (v2_pre_topc @ sk_B)
% 0.85/1.06        | ~ (m1_pre_topc @ sk_A @ sk_B)
% 0.85/1.06        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['48', '52'])).
% 0.85/1.06  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('55', plain, ((v2_pre_topc @ sk_B)),
% 0.85/1.06      inference('demod', [status(thm)], ['34', '39', '40'])).
% 0.85/1.06  thf('56', plain,
% 0.85/1.06      ((m1_pre_topc @ 
% 0.85/1.06        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)),
% 0.85/1.06      inference('demod', [status(thm)], ['21', '22'])).
% 0.85/1.06  thf('57', plain,
% 0.85/1.06      ((l1_pre_topc @ 
% 0.85/1.06        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.85/1.06      inference('demod', [status(thm)], ['25', '26'])).
% 0.85/1.06  thf('58', plain,
% 0.85/1.06      (![X28 : $i, X29 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X29)
% 0.85/1.06          | ~ (v2_pre_topc @ X28)
% 0.85/1.06          | ~ (l1_pre_topc @ X28)
% 0.85/1.06          | (m1_pre_topc @ X28 @ X29)
% 0.85/1.06          | ~ (m1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)) @ X29)
% 0.85/1.06          | ~ (l1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)))
% 0.85/1.06          | ~ (v2_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28))))),
% 0.85/1.06      inference('simplify', [status(thm)], ['10'])).
% 0.85/1.06  thf('59', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (v2_pre_topc @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.85/1.06          | ~ (m1_pre_topc @ 
% 0.85/1.06               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ X0)
% 0.85/1.06          | (m1_pre_topc @ sk_A @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ sk_A)
% 0.85/1.06          | ~ (v2_pre_topc @ sk_A)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['57', '58'])).
% 0.85/1.06  thf('60', plain,
% 0.85/1.06      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.85/1.06         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('61', plain,
% 0.85/1.06      (![X12 : $i]:
% 0.85/1.06         ((v2_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 0.85/1.06          | ~ (l1_pre_topc @ X12)
% 0.85/1.06          | ~ (v2_pre_topc @ X12))),
% 0.85/1.06      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.85/1.06  thf('62', plain,
% 0.85/1.06      (((v2_pre_topc @ 
% 0.85/1.06         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.85/1.06        | ~ (v2_pre_topc @ sk_B)
% 0.85/1.06        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.06      inference('sup+', [status(thm)], ['60', '61'])).
% 0.85/1.06  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('64', plain,
% 0.85/1.06      (((v2_pre_topc @ 
% 0.85/1.06         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.85/1.06        | ~ (v2_pre_topc @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['62', '63'])).
% 0.85/1.06  thf('65', plain, ((v2_pre_topc @ sk_B)),
% 0.85/1.06      inference('demod', [status(thm)], ['34', '39', '40'])).
% 0.85/1.06  thf('66', plain,
% 0.85/1.06      ((v2_pre_topc @ 
% 0.85/1.06        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.85/1.06      inference('demod', [status(thm)], ['64', '65'])).
% 0.85/1.06  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.85/1.06      inference('demod', [status(thm)], ['37', '38'])).
% 0.85/1.06  thf('69', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ X0)
% 0.85/1.06          | (m1_pre_topc @ sk_A @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('demod', [status(thm)], ['59', '66', '67', '68'])).
% 0.85/1.06  thf('70', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.85/1.06      inference('sup-', [status(thm)], ['56', '69'])).
% 0.85/1.06  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('72', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.85/1.06      inference('demod', [status(thm)], ['70', '71'])).
% 0.85/1.06  thf('73', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.85/1.06      inference('demod', [status(thm)], ['53', '54', '55', '72'])).
% 0.85/1.06  thf(d10_xboole_0, axiom,
% 0.85/1.06    (![A:$i,B:$i]:
% 0.85/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.85/1.06  thf('74', plain,
% 0.85/1.06      (![X0 : $i, X2 : $i]:
% 0.85/1.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.85/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.06  thf('75', plain,
% 0.85/1.06      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.85/1.06        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['73', '74'])).
% 0.85/1.06  thf('76', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.85/1.06      inference('demod', [status(thm)], ['70', '71'])).
% 0.85/1.06  thf('77', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ X0 @ X1)
% 0.85/1.06          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.85/1.06          | ~ (m1_pre_topc @ X1 @ X0)
% 0.85/1.06          | ~ (v2_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['51'])).
% 0.85/1.06  thf('78', plain,
% 0.85/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.85/1.06        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.85/1.06        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['76', '77'])).
% 0.85/1.06  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.85/1.06      inference('demod', [status(thm)], ['37', '38'])).
% 0.85/1.06  thf('81', plain,
% 0.85/1.06      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.85/1.06        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.85/1.06      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.85/1.06  thf('82', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.85/1.06      inference('demod', [status(thm)], ['46', '47'])).
% 0.85/1.06  thf('83', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['81', '82'])).
% 0.85/1.06  thf('84', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['75', '83'])).
% 0.85/1.06  thf(dt_k2_subset_1, axiom,
% 0.85/1.06    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.85/1.06  thf('85', plain,
% 0.85/1.06      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.85/1.06      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.85/1.06  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.85/1.06  thf('86', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.85/1.06      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.85/1.06  thf(redefinition_k9_setfam_1, axiom,
% 0.85/1.06    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.85/1.06  thf('87', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('88', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k9_setfam_1 @ X4))),
% 0.85/1.06      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.85/1.06  thf(t78_tops_2, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ![B:$i]:
% 0.85/1.06         ( ( m1_subset_1 @
% 0.85/1.06             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.85/1.06           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.85/1.06  thf('89', plain,
% 0.85/1.06      (![X23 : $i, X24 : $i]:
% 0.85/1.06         (~ (m1_subset_1 @ X23 @ 
% 0.85/1.06             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 0.85/1.06          | ~ (v1_tops_2 @ X23 @ X24)
% 0.85/1.06          | (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.85/1.06          | ~ (l1_pre_topc @ X24))),
% 0.85/1.06      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.85/1.06  thf('90', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('91', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('92', plain,
% 0.85/1.06      (![X23 : $i, X24 : $i]:
% 0.85/1.06         (~ (m1_subset_1 @ X23 @ 
% 0.85/1.06             (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X24))))
% 0.85/1.06          | ~ (v1_tops_2 @ X23 @ X24)
% 0.85/1.06          | (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.85/1.06          | ~ (l1_pre_topc @ X24))),
% 0.85/1.06      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.85/1.06  thf('93', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | (r1_tarski @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ 
% 0.85/1.06             (u1_pre_topc @ X0))
% 0.85/1.06          | ~ (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['88', '92'])).
% 0.85/1.06  thf('94', plain,
% 0.85/1.06      ((~ (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.85/1.06        | (r1_tarski @ (k9_setfam_1 @ (u1_struct_0 @ sk_B)) @ 
% 0.85/1.06           (u1_pre_topc @ sk_B))
% 0.85/1.06        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.06      inference('sup-', [status(thm)], ['84', '93'])).
% 0.85/1.06  thf('95', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['75', '83'])).
% 0.85/1.06  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('97', plain,
% 0.85/1.06      ((~ (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.85/1.06        | (r1_tarski @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.85/1.06           (u1_pre_topc @ sk_B)))),
% 0.85/1.06      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.85/1.06  thf(d1_tdlat_3, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ( v1_tdlat_3 @ A ) <=>
% 0.85/1.06         ( ( u1_pre_topc @ A ) = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.85/1.06  thf('98', plain,
% 0.85/1.06      (![X38 : $i]:
% 0.85/1.06         (~ (v1_tdlat_3 @ X38)
% 0.85/1.06          | ((u1_pre_topc @ X38) = (k9_setfam_1 @ (u1_struct_0 @ X38)))
% 0.85/1.06          | ~ (l1_pre_topc @ X38))),
% 0.85/1.06      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.85/1.06  thf('99', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k9_setfam_1 @ X4))),
% 0.85/1.06      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.85/1.06  thf('100', plain,
% 0.85/1.06      (![X23 : $i, X24 : $i]:
% 0.85/1.06         (~ (m1_subset_1 @ X23 @ 
% 0.85/1.06             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 0.85/1.06          | ~ (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.85/1.06          | (v1_tops_2 @ X23 @ X24)
% 0.85/1.06          | ~ (l1_pre_topc @ X24))),
% 0.85/1.06      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.85/1.06  thf('101', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('102', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('103', plain,
% 0.85/1.06      (![X23 : $i, X24 : $i]:
% 0.85/1.06         (~ (m1_subset_1 @ X23 @ 
% 0.85/1.06             (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X24))))
% 0.85/1.06          | ~ (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.85/1.06          | (v1_tops_2 @ X23 @ X24)
% 0.85/1.06          | ~ (l1_pre_topc @ X24))),
% 0.85/1.06      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.85/1.06  thf('104', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ X0)
% 0.85/1.06          | ~ (r1_tarski @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ 
% 0.85/1.06               (u1_pre_topc @ X0)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['99', '103'])).
% 0.85/1.06  thf('105', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (r1_tarski @ (u1_pre_topc @ X0) @ (u1_pre_topc @ X0))
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (v1_tdlat_3 @ X0)
% 0.85/1.06          | (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['98', '104'])).
% 0.85/1.06  thf('106', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.85/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.06  thf('107', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.85/1.06      inference('simplify', [status(thm)], ['106'])).
% 0.85/1.06  thf('108', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (v1_tdlat_3 @ X0)
% 0.85/1.06          | (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('demod', [status(thm)], ['105', '107'])).
% 0.85/1.06  thf('109', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         ((v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ X0)
% 0.85/1.06          | ~ (v1_tdlat_3 @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['108'])).
% 0.85/1.06  thf('110', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | (r1_tarski @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ 
% 0.85/1.06             (u1_pre_topc @ X0))
% 0.85/1.06          | ~ (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['88', '92'])).
% 0.85/1.06  thf('111', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (v1_tdlat_3 @ X0)
% 0.85/1.06          | (r1_tarski @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ 
% 0.85/1.06             (u1_pre_topc @ X0))
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['109', '110'])).
% 0.85/1.06  thf('112', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         ((r1_tarski @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ (u1_pre_topc @ X0))
% 0.85/1.06          | ~ (v1_tdlat_3 @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['111'])).
% 0.85/1.06  thf('113', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         ((m1_pre_topc @ 
% 0.85/1.06           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('simplify', [status(thm)], ['5'])).
% 0.85/1.06  thf('114', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ 
% 0.85/1.06             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ X0)
% 0.85/1.06          | (m1_pre_topc @ sk_A @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X0))),
% 0.85/1.06      inference('demod', [status(thm)], ['59', '66', '67', '68'])).
% 0.85/1.06  thf('115', plain,
% 0.85/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.85/1.06        | (m1_pre_topc @ sk_A @ sk_A))),
% 0.85/1.06      inference('sup-', [status(thm)], ['113', '114'])).
% 0.85/1.06  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('118', plain, ((m1_pre_topc @ sk_A @ sk_A)),
% 0.85/1.06      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.85/1.06  thf(dt_u1_pre_topc, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( m1_subset_1 @
% 0.85/1.06         ( u1_pre_topc @ A ) @ 
% 0.85/1.06         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.85/1.06  thf('119', plain,
% 0.85/1.06      (![X11 : $i]:
% 0.85/1.06         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.85/1.06           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.85/1.06          | ~ (l1_pre_topc @ X11))),
% 0.85/1.06      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.85/1.06  thf('120', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('121', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('122', plain,
% 0.85/1.06      (![X11 : $i]:
% 0.85/1.06         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.85/1.06           (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X11))))
% 0.85/1.06          | ~ (l1_pre_topc @ X11))),
% 0.85/1.06      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.85/1.06  thf(t31_tops_2, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ![B:$i]:
% 0.85/1.06         ( ( m1_pre_topc @ B @ A ) =>
% 0.85/1.06           ( ![C:$i]:
% 0.85/1.06             ( ( m1_subset_1 @
% 0.85/1.06                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.85/1.06               ( m1_subset_1 @
% 0.85/1.06                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.85/1.06  thf('123', plain,
% 0.85/1.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ X16 @ X17)
% 0.85/1.06          | (m1_subset_1 @ X18 @ 
% 0.85/1.06             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.85/1.06          | ~ (m1_subset_1 @ X18 @ 
% 0.85/1.06               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.85/1.06          | ~ (l1_pre_topc @ X17))),
% 0.85/1.06      inference('cnf', [status(esa)], [t31_tops_2])).
% 0.85/1.06  thf('124', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('125', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('126', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('127', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('128', plain,
% 0.85/1.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.85/1.06         (~ (m1_pre_topc @ X16 @ X17)
% 0.85/1.06          | (m1_subset_1 @ X18 @ 
% 0.85/1.06             (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X17))))
% 0.85/1.06          | ~ (m1_subset_1 @ X18 @ 
% 0.85/1.06               (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X16))))
% 0.85/1.06          | ~ (l1_pre_topc @ X17))),
% 0.85/1.06      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 0.85/1.06  thf('129', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (l1_pre_topc @ X1)
% 0.85/1.06          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.85/1.06             (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X1))))
% 0.85/1.06          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['122', '128'])).
% 0.85/1.06  thf('130', plain,
% 0.85/1.06      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.85/1.06         (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))
% 0.85/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.85/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.85/1.06      inference('sup-', [status(thm)], ['118', '129'])).
% 0.85/1.06  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('133', plain,
% 0.85/1.06      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.85/1.06        (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))),
% 0.85/1.06      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.85/1.06  thf(t3_subset, axiom,
% 0.85/1.06    (![A:$i,B:$i]:
% 0.85/1.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.85/1.06  thf('134', plain,
% 0.85/1.06      (![X5 : $i, X6 : $i]:
% 0.85/1.06         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.85/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.85/1.06  thf('135', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('136', plain,
% 0.85/1.06      (![X5 : $i, X6 : $i]:
% 0.85/1.06         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k9_setfam_1 @ X6)))),
% 0.85/1.06      inference('demod', [status(thm)], ['134', '135'])).
% 0.85/1.06  thf('137', plain,
% 0.85/1.06      ((r1_tarski @ (u1_pre_topc @ sk_A) @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['133', '136'])).
% 0.85/1.06  thf('138', plain,
% 0.85/1.06      (![X0 : $i, X2 : $i]:
% 0.85/1.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.85/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.06  thf('139', plain,
% 0.85/1.06      ((~ (r1_tarski @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.85/1.06           (u1_pre_topc @ sk_A))
% 0.85/1.06        | ((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_A)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['137', '138'])).
% 0.85/1.06  thf('140', plain,
% 0.85/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.06        | ~ (v1_tdlat_3 @ sk_A)
% 0.85/1.06        | ((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_A)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['112', '139'])).
% 0.85/1.06  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('142', plain, ((v1_tdlat_3 @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('143', plain,
% 0.85/1.06      (((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.85/1.06      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.85/1.06  thf('144', plain,
% 0.85/1.06      (((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.85/1.06      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.85/1.06  thf('145', plain,
% 0.85/1.06      ((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.85/1.06        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B)))),
% 0.85/1.06      inference('demod', [status(thm)], ['97', '143', '144'])).
% 0.85/1.06  thf('146', plain,
% 0.85/1.06      (![X38 : $i]:
% 0.85/1.06         (~ (v1_tdlat_3 @ X38)
% 0.85/1.06          | ((u1_pre_topc @ X38) = (k9_setfam_1 @ (u1_struct_0 @ X38)))
% 0.85/1.06          | ~ (l1_pre_topc @ X38))),
% 0.85/1.06      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.85/1.06  thf('147', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['75', '83'])).
% 0.85/1.06  thf('148', plain,
% 0.85/1.06      (![X11 : $i]:
% 0.85/1.06         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.85/1.06           (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X11))))
% 0.85/1.06          | ~ (l1_pre_topc @ X11))),
% 0.85/1.06      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.85/1.06  thf('149', plain,
% 0.85/1.06      (![X5 : $i, X6 : $i]:
% 0.85/1.06         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k9_setfam_1 @ X6)))),
% 0.85/1.06      inference('demod', [status(thm)], ['134', '135'])).
% 0.85/1.06  thf('150', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X0)
% 0.85/1.06          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.85/1.06             (k9_setfam_1 @ (u1_struct_0 @ X0))))),
% 0.85/1.06      inference('sup-', [status(thm)], ['148', '149'])).
% 0.85/1.06  thf('151', plain,
% 0.85/1.06      (((r1_tarski @ (u1_pre_topc @ sk_B) @ 
% 0.85/1.06         (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.85/1.06        | ~ (l1_pre_topc @ sk_B))),
% 0.85/1.06      inference('sup+', [status(thm)], ['147', '150'])).
% 0.85/1.06  thf('152', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('153', plain,
% 0.85/1.06      ((r1_tarski @ (u1_pre_topc @ sk_B) @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.06      inference('demod', [status(thm)], ['151', '152'])).
% 0.85/1.06  thf('154', plain,
% 0.85/1.06      (((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.85/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.85/1.06        | ~ (v1_tdlat_3 @ sk_A))),
% 0.85/1.06      inference('sup+', [status(thm)], ['146', '153'])).
% 0.85/1.06  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('156', plain, ((v1_tdlat_3 @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('157', plain,
% 0.85/1.06      ((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.85/1.06      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.85/1.06  thf('158', plain,
% 0.85/1.06      (![X0 : $i, X2 : $i]:
% 0.85/1.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.85/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.06  thf('159', plain,
% 0.85/1.06      ((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.85/1.06        | ((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['157', '158'])).
% 0.85/1.06  thf('160', plain,
% 0.85/1.06      (![X38 : $i]:
% 0.85/1.06         (~ (v1_tdlat_3 @ X38)
% 0.85/1.06          | ((u1_pre_topc @ X38) = (k9_setfam_1 @ (u1_struct_0 @ X38)))
% 0.85/1.06          | ~ (l1_pre_topc @ X38))),
% 0.85/1.06      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.85/1.06  thf('161', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['75', '83'])).
% 0.85/1.06  thf('162', plain,
% 0.85/1.06      (![X38 : $i]:
% 0.85/1.06         (((u1_pre_topc @ X38) != (k9_setfam_1 @ (u1_struct_0 @ X38)))
% 0.85/1.06          | (v1_tdlat_3 @ X38)
% 0.85/1.06          | ~ (l1_pre_topc @ X38))),
% 0.85/1.06      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.85/1.06  thf('163', plain,
% 0.85/1.06      ((((u1_pre_topc @ sk_B) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.85/1.06        | ~ (l1_pre_topc @ sk_B)
% 0.85/1.06        | (v1_tdlat_3 @ sk_B))),
% 0.85/1.06      inference('sup-', [status(thm)], ['161', '162'])).
% 0.85/1.06  thf('164', plain, ((l1_pre_topc @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('165', plain,
% 0.85/1.06      ((((u1_pre_topc @ sk_B) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.85/1.06        | (v1_tdlat_3 @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['163', '164'])).
% 0.85/1.06  thf('166', plain, (~ (v1_tdlat_3 @ sk_B)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('167', plain,
% 0.85/1.06      (((u1_pre_topc @ sk_B) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.85/1.06      inference('clc', [status(thm)], ['165', '166'])).
% 0.85/1.06  thf('168', plain,
% 0.85/1.06      ((((u1_pre_topc @ sk_B) != (u1_pre_topc @ sk_A))
% 0.85/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.85/1.06        | ~ (v1_tdlat_3 @ sk_A))),
% 0.85/1.06      inference('sup-', [status(thm)], ['160', '167'])).
% 0.85/1.06  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('170', plain, ((v1_tdlat_3 @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('171', plain, (((u1_pre_topc @ sk_B) != (u1_pre_topc @ sk_A))),
% 0.85/1.06      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.85/1.06  thf('172', plain,
% 0.85/1.06      (~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))),
% 0.85/1.06      inference('simplify_reflect-', [status(thm)], ['159', '171'])).
% 0.85/1.06  thf('173', plain, (~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)),
% 0.85/1.06      inference('clc', [status(thm)], ['145', '172'])).
% 0.85/1.06  thf('174', plain,
% 0.85/1.06      (![X11 : $i]:
% 0.85/1.06         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.85/1.06           (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X11))))
% 0.85/1.06          | ~ (l1_pre_topc @ X11))),
% 0.85/1.06      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.85/1.06  thf('175', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['75', '83'])).
% 0.85/1.06  thf('176', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k9_setfam_1 @ X4))),
% 0.85/1.06      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.85/1.06  thf(t35_tops_2, axiom,
% 0.85/1.06    (![A:$i]:
% 0.85/1.06     ( ( l1_pre_topc @ A ) =>
% 0.85/1.06       ( ![B:$i]:
% 0.85/1.06         ( ( m1_subset_1 @
% 0.85/1.06             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.85/1.06           ( ![C:$i]:
% 0.85/1.06             ( ( m1_pre_topc @ C @ A ) =>
% 0.85/1.06               ( ( v1_tops_2 @ B @ A ) =>
% 0.85/1.06                 ( ![D:$i]:
% 0.85/1.06                   ( ( m1_subset_1 @
% 0.85/1.06                       D @ 
% 0.85/1.06                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.85/1.06                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.85/1.06  thf('177', plain,
% 0.85/1.06      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.85/1.06         (~ (m1_subset_1 @ X19 @ 
% 0.85/1.06             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.85/1.06          | ~ (v1_tops_2 @ X19 @ X20)
% 0.85/1.06          | ~ (m1_subset_1 @ X21 @ 
% 0.85/1.06               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))
% 0.85/1.06          | (v1_tops_2 @ X21 @ X22)
% 0.85/1.06          | ((X21) != (X19))
% 0.85/1.06          | ~ (m1_pre_topc @ X22 @ X20)
% 0.85/1.06          | ~ (l1_pre_topc @ X20))),
% 0.85/1.06      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.85/1.06  thf('178', plain,
% 0.85/1.06      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X20)
% 0.85/1.06          | ~ (m1_pre_topc @ X22 @ X20)
% 0.85/1.06          | (v1_tops_2 @ X19 @ X22)
% 0.85/1.06          | ~ (m1_subset_1 @ X19 @ 
% 0.85/1.06               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))
% 0.85/1.06          | ~ (v1_tops_2 @ X19 @ X20)
% 0.85/1.06          | ~ (m1_subset_1 @ X19 @ 
% 0.85/1.06               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))))),
% 0.85/1.06      inference('simplify', [status(thm)], ['177'])).
% 0.85/1.06  thf('179', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('180', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('181', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('182', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.85/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.85/1.06  thf('183', plain,
% 0.85/1.06      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.85/1.06         (~ (l1_pre_topc @ X20)
% 0.85/1.06          | ~ (m1_pre_topc @ X22 @ X20)
% 0.85/1.06          | (v1_tops_2 @ X19 @ X22)
% 0.85/1.06          | ~ (m1_subset_1 @ X19 @ 
% 0.85/1.06               (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X22))))
% 0.85/1.06          | ~ (v1_tops_2 @ X19 @ X20)
% 0.85/1.06          | ~ (m1_subset_1 @ X19 @ 
% 0.85/1.06               (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X20)))))),
% 0.85/1.06      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 0.85/1.06  thf('184', plain,
% 0.85/1.06      (![X0 : $i, X1 : $i]:
% 0.85/1.06         (~ (m1_subset_1 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ 
% 0.85/1.06             (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X1))))
% 0.85/1.06          | ~ (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ X1)
% 0.85/1.06          | (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ X0)) @ X0)
% 0.85/1.06          | ~ (m1_pre_topc @ X0 @ X1)
% 0.85/1.06          | ~ (l1_pre_topc @ X1))),
% 0.85/1.06      inference('sup-', [status(thm)], ['176', '183'])).
% 0.85/1.06  thf('185', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (m1_subset_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.85/1.06             (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X0))))
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.85/1.06          | (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_B)) @ sk_B)
% 0.85/1.06          | ~ (v1_tops_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_B)) @ X0))),
% 0.85/1.06      inference('sup-', [status(thm)], ['175', '184'])).
% 0.85/1.06  thf('186', plain,
% 0.85/1.06      (((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.85/1.06      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.85/1.06  thf('187', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['75', '83'])).
% 0.85/1.06  thf('188', plain,
% 0.85/1.06      (((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.85/1.06      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.85/1.06  thf('189', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.85/1.06      inference('demod', [status(thm)], ['75', '83'])).
% 0.85/1.06  thf('190', plain,
% 0.85/1.06      (((k9_setfam_1 @ (u1_struct_0 @ sk_A)) = (u1_pre_topc @ sk_A))),
% 0.85/1.06      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.85/1.06  thf('191', plain,
% 0.85/1.06      (![X0 : $i]:
% 0.85/1.06         (~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.85/1.06             (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X0))))
% 0.85/1.06          | ~ (l1_pre_topc @ X0)
% 0.85/1.06          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.85/1.06          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.85/1.06          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0))),
% 0.85/1.06      inference('demod', [status(thm)],
% 0.85/1.06                ['185', '186', '187', '188', '189', '190'])).
% 0.85/1.06  thf('192', plain,
% 0.85/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.06        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.85/1.06        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.85/1.06        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.85/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.85/1.06      inference('sup-', [status(thm)], ['174', '191'])).
% 0.85/1.06  thf('193', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('194', plain,
% 0.85/1.06      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.85/1.06        (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))),
% 0.85/1.06      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.85/1.06  thf('195', plain,
% 0.85/1.06      (![X23 : $i, X24 : $i]:
% 0.85/1.06         (~ (m1_subset_1 @ X23 @ 
% 0.85/1.06             (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ X24))))
% 0.85/1.06          | ~ (r1_tarski @ X23 @ (u1_pre_topc @ X24))
% 0.85/1.06          | (v1_tops_2 @ X23 @ X24)
% 0.85/1.06          | ~ (l1_pre_topc @ X24))),
% 0.85/1.06      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.85/1.06  thf('196', plain,
% 0.85/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.85/1.06        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.85/1.06        | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.85/1.06      inference('sup-', [status(thm)], ['194', '195'])).
% 0.85/1.06  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('198', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.85/1.06      inference('simplify', [status(thm)], ['106'])).
% 0.85/1.06  thf('199', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.85/1.06      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.85/1.06  thf('200', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.85/1.06      inference('demod', [status(thm)], ['46', '47'])).
% 0.85/1.06  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.06  thf('202', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)),
% 0.85/1.06      inference('demod', [status(thm)], ['192', '193', '199', '200', '201'])).
% 0.85/1.06  thf('203', plain, ($false), inference('demod', [status(thm)], ['173', '202'])).
% 0.85/1.06  
% 0.85/1.06  % SZS output end Refutation
% 0.85/1.06  
% 0.85/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
