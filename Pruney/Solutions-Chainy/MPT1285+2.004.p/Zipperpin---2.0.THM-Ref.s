%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KG3oK2yvik

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:55 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 376 expanded)
%              Number of leaves         :   30 ( 112 expanded)
%              Depth                    :   15
%              Number of atoms          : 1299 (6677 expanded)
%              Number of equality atoms :   31 (  53 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t107_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( v3_pre_topc @ D @ B )
                        & ( v4_tops_1 @ D @ B ) )
                     => ( v6_tops_1 @ D @ B ) )
                    & ( ( v6_tops_1 @ C @ A )
                     => ( ( v3_pre_topc @ C @ A )
                        & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( ( v3_pre_topc @ D @ B )
                          & ( v4_tops_1 @ D @ B ) )
                       => ( v6_tops_1 @ D @ B ) )
                      & ( ( v6_tops_1 @ C @ A )
                       => ( ( v3_pre_topc @ C @ A )
                          & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_tops_1])).

thf('0',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v6_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v6_tops_1 @ X17 @ X18 )
      | ( X17
        = ( k1_tops_1 @ X18 @ ( k2_pre_topc @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X21 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('18',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('25',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('31',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','31'])).

thf('33',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k1_tops_1 @ X14 @ X13 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k2_pre_topc @ X14 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X16 @ ( k2_pre_topc @ X16 @ X15 ) ) @ X15 )
      | ~ ( r1_tarski @ X15 @ ( k2_pre_topc @ X16 @ ( k1_tops_1 @ X16 @ X15 ) ) )
      | ( v4_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ X9 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['53','58','59','61'])).

thf('63',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('70',plain,
    ( ( v6_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('72',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('73',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['67'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X26 )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( r1_tarski @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ X9 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['65'])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_tops_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ ( k2_pre_topc @ X16 @ X15 ) ) @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( X17
       != ( k1_tops_1 @ X18 @ ( k2_pre_topc @ X18 @ X17 ) ) )
      | ( v6_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('111',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['1','3','66','68','69','70','73','111'])).

thf('113',plain,(
    ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['64','112'])).

thf('114',plain,(
    ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['62','113'])).

thf('115',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('116',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','114','115','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KG3oK2yvik
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 252 iterations in 0.157s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.62  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.37/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.62  thf(t107_tops_1, conjecture,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( l1_pre_topc @ B ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62               ( ![D:$i]:
% 0.37/0.62                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.62                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.37/0.62                       ( v6_tops_1 @ D @ B ) ) & 
% 0.37/0.62                     ( ( v6_tops_1 @ C @ A ) =>
% 0.37/0.62                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i]:
% 0.37/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62          ( ![B:$i]:
% 0.37/0.62            ( ( l1_pre_topc @ B ) =>
% 0.37/0.62              ( ![C:$i]:
% 0.37/0.62                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62                  ( ![D:$i]:
% 0.37/0.62                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.62                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.37/0.62                          ( v6_tops_1 @ D @ B ) ) & 
% 0.37/0.62                        ( ( v6_tops_1 @ C @ A ) =>
% 0.37/0.62                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.37/0.62  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['2'])).
% 0.37/0.62  thf('4', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['4'])).
% 0.37/0.62  thf('6', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(d8_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( v6_tops_1 @ B @ A ) <=>
% 0.37/0.62             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf('7', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.62          | ~ (v6_tops_1 @ X17 @ X18)
% 0.37/0.62          | ((X17) = (k1_tops_1 @ X18 @ (k2_pre_topc @ X18 @ X17)))
% 0.37/0.62          | ~ (l1_pre_topc @ X18))),
% 0.37/0.62      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.37/0.62        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.62  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.37/0.62        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.62  thf('11', plain,
% 0.37/0.62      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.37/0.62         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(dt_k2_pre_topc, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62       ( m1_subset_1 @
% 0.37/0.62         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X7)
% 0.37/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.37/0.62          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.37/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.62  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf(fc9_tops_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      (![X21 : $i, X22 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X21)
% 0.37/0.62          | ~ (v2_pre_topc @ X21)
% 0.37/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.62          | (v3_pre_topc @ (k1_tops_1 @ X21 @ X22) @ X21))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)
% 0.37/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.62  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)),
% 0.37/0.62      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['11', '21'])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(dt_k3_subset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.62       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.62  thf('24', plain,
% 0.37/0.62      (![X3 : $i, X4 : $i]:
% 0.37/0.62         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 0.37/0.62          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.62  thf('25', plain,
% 0.37/0.62      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf(t29_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.62             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.37/0.62  thf('26', plain,
% 0.37/0.62      (![X23 : $i, X24 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.37/0.62          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.37/0.62          | (v4_pre_topc @ X23 @ X24)
% 0.37/0.62          | ~ (l1_pre_topc @ X24))),
% 0.37/0.62      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.37/0.62  thf('27', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.37/0.62        | ~ (v3_pre_topc @ 
% 0.37/0.62             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.62              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.37/0.62             sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.62  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(involutiveness_k3_subset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.62       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      (![X5 : $i, X6 : $i]:
% 0.37/0.62         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.37/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.37/0.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 0.37/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.37/0.62        | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['27', '28', '31'])).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))
% 0.37/0.62         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['22', '32'])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf(t52_pre_topc, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.37/0.62             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.37/0.62               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      (![X11 : $i, X12 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.62          | ~ (v4_pre_topc @ X11 @ X12)
% 0.37/0.62          | ((k2_pre_topc @ X12 @ X11) = (X11))
% 0.37/0.62          | ~ (l1_pre_topc @ X12))),
% 0.37/0.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.62  thf('36', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.62            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.62        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.62  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('38', plain,
% 0.37/0.62      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.62          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.62        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.62  thf('39', plain,
% 0.37/0.62      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.62          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.37/0.62         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['33', '38'])).
% 0.37/0.62  thf('40', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(d1_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( k1_tops_1 @ A @ B ) =
% 0.37/0.62             ( k3_subset_1 @
% 0.37/0.62               ( u1_struct_0 @ A ) @ 
% 0.37/0.62               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf('41', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.62          | ((k1_tops_1 @ X14 @ X13)
% 0.37/0.62              = (k3_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.37/0.62                 (k2_pre_topc @ X14 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13))))
% 0.37/0.62          | ~ (l1_pre_topc @ X14))),
% 0.37/0.62      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.37/0.62  thf('42', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | ((k1_tops_1 @ sk_A @ sk_C)
% 0.37/0.62            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.62               (k2_pre_topc @ sk_A @ 
% 0.37/0.62                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.62  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('44', plain,
% 0.37/0.62      (((k1_tops_1 @ sk_A @ sk_C)
% 0.37/0.62         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.62            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.37/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.62  thf('45', plain,
% 0.37/0.62      ((((k1_tops_1 @ sk_A @ sk_C)
% 0.37/0.62          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.62             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.37/0.62         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['39', '44'])).
% 0.37/0.62  thf('46', plain,
% 0.37/0.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 0.37/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.62  thf('47', plain,
% 0.37/0.62      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['45', '46'])).
% 0.37/0.62  thf('48', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(d6_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( v4_tops_1 @ B @ A ) <=>
% 0.37/0.62             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.37/0.62               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf('49', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.62          | ~ (r1_tarski @ (k1_tops_1 @ X16 @ (k2_pre_topc @ X16 @ X15)) @ X15)
% 0.37/0.62          | ~ (r1_tarski @ X15 @ (k2_pre_topc @ X16 @ (k1_tops_1 @ X16 @ X15)))
% 0.37/0.62          | (v4_tops_1 @ X15 @ X16)
% 0.37/0.62          | ~ (l1_pre_topc @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.37/0.62  thf('50', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | (v4_tops_1 @ sk_C @ sk_A)
% 0.37/0.62        | ~ (r1_tarski @ sk_C @ 
% 0.37/0.62             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.62             sk_C))),
% 0.37/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.62  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('52', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_C @ sk_A)
% 0.37/0.62        | ~ (r1_tarski @ sk_C @ 
% 0.37/0.62             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.62             sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.62  thf('53', plain,
% 0.37/0.62      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.37/0.62         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.62              sk_C)
% 0.37/0.62         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['47', '52'])).
% 0.37/0.62  thf('54', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t48_pre_topc, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.37/0.62  thf('55', plain,
% 0.37/0.62      (![X9 : $i, X10 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.37/0.62          | (r1_tarski @ X9 @ (k2_pre_topc @ X10 @ X9))
% 0.37/0.62          | ~ (l1_pre_topc @ X10))),
% 0.37/0.62      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.37/0.62  thf('56', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.62  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('58', plain, ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.62  thf('59', plain,
% 0.37/0.62      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.37/0.62         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.62  thf(d10_xboole_0, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.62  thf('60', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.62  thf('61', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.62      inference('simplify', [status(thm)], ['60'])).
% 0.37/0.62  thf('62', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['53', '58', '59', '61'])).
% 0.37/0.62  thf('63', plain,
% 0.37/0.62      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.37/0.62        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('64', plain,
% 0.37/0.62      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['63'])).
% 0.37/0.62  thf('65', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_D @ sk_B)
% 0.37/0.62        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('66', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_tops_1 @ sk_C @ sk_A)) | 
% 0.37/0.62       ~ ((v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['65'])).
% 0.37/0.62  thf('67', plain,
% 0.37/0.62      (((v3_pre_topc @ sk_D @ sk_B)
% 0.37/0.62        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('68', plain,
% 0.37/0.62      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v4_tops_1 @ sk_C @ sk_A)) | 
% 0.37/0.62       ~ ((v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['67'])).
% 0.37/0.62  thf('69', plain,
% 0.37/0.62      (~ ((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.37/0.62       ~ ((v6_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('split', [status(esa)], ['63'])).
% 0.37/0.62  thf('70', plain,
% 0.37/0.62      (((v6_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('split', [status(esa)], ['4'])).
% 0.37/0.62  thf('71', plain,
% 0.37/0.62      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['11', '21'])).
% 0.37/0.62  thf('72', plain,
% 0.37/0.62      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['63'])).
% 0.37/0.62  thf('73', plain,
% 0.37/0.62      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.62  thf('74', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('75', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X7)
% 0.37/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.37/0.62          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.62  thf('76', plain,
% 0.37/0.62      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.37/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.37/0.62  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('78', plain,
% 0.37/0.62      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.37/0.62  thf('79', plain,
% 0.37/0.62      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['67'])).
% 0.37/0.62  thf('80', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t56_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.62                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf('81', plain,
% 0.37/0.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.37/0.62          | ~ (v3_pre_topc @ X25 @ X26)
% 0.37/0.62          | ~ (r1_tarski @ X25 @ X27)
% 0.37/0.62          | (r1_tarski @ X25 @ (k1_tops_1 @ X26 @ X27))
% 0.37/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.37/0.62          | ~ (l1_pre_topc @ X26))),
% 0.37/0.62      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.37/0.62  thf('82', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.62          | ~ (r1_tarski @ sk_D @ X0)
% 0.37/0.62          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.37/0.62  thf('83', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('84', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.62          | ~ (r1_tarski @ sk_D @ X0)
% 0.37/0.62          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.37/0.62  thf('85', plain,
% 0.37/0.62      ((![X0 : $i]:
% 0.37/0.62          (~ (r1_tarski @ sk_D @ X0)
% 0.37/0.62           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.62           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.37/0.62         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['79', '84'])).
% 0.37/0.62  thf('86', plain,
% 0.37/0.62      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.37/0.62         | ~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.37/0.62         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['78', '85'])).
% 0.37/0.62  thf('87', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('88', plain,
% 0.37/0.62      (![X9 : $i, X10 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.37/0.62          | (r1_tarski @ X9 @ (k2_pre_topc @ X10 @ X9))
% 0.37/0.62          | ~ (l1_pre_topc @ X10))),
% 0.37/0.62      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.37/0.62  thf('89', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.37/0.62  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('91', plain, ((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['89', '90'])).
% 0.37/0.62  thf('92', plain,
% 0.37/0.62      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.37/0.62         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['86', '91'])).
% 0.37/0.62  thf('93', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['65'])).
% 0.37/0.62  thf('94', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('95', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.62          | ~ (v4_tops_1 @ X15 @ X16)
% 0.37/0.62          | (r1_tarski @ (k1_tops_1 @ X16 @ (k2_pre_topc @ X16 @ X15)) @ X15)
% 0.37/0.62          | ~ (l1_pre_topc @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.37/0.62  thf('96', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['94', '95'])).
% 0.37/0.62  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('98', plain,
% 0.37/0.62      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['96', '97'])).
% 0.37/0.62  thf('99', plain,
% 0.37/0.62      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['93', '98'])).
% 0.37/0.62  thf('100', plain,
% 0.37/0.62      (![X0 : $i, X2 : $i]:
% 0.37/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.62  thf('101', plain,
% 0.37/0.62      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.37/0.62         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.37/0.62  thf('102', plain,
% 0.37/0.62      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['92', '101'])).
% 0.37/0.62  thf('103', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('104', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.62          | ((X17) != (k1_tops_1 @ X18 @ (k2_pre_topc @ X18 @ X17)))
% 0.37/0.62          | (v6_tops_1 @ X17 @ X18)
% 0.37/0.62          | ~ (l1_pre_topc @ X18))),
% 0.37/0.62      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.37/0.62  thf('105', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | (v6_tops_1 @ sk_D @ sk_B)
% 0.37/0.62        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['103', '104'])).
% 0.37/0.62  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('107', plain,
% 0.37/0.62      (((v6_tops_1 @ sk_D @ sk_B)
% 0.37/0.62        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.37/0.62      inference('demod', [status(thm)], ['105', '106'])).
% 0.37/0.62  thf('108', plain,
% 0.37/0.62      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['102', '107'])).
% 0.37/0.62  thf('109', plain,
% 0.37/0.62      (((v6_tops_1 @ sk_D @ sk_B))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['108'])).
% 0.37/0.62  thf('110', plain,
% 0.37/0.62      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['63'])).
% 0.37/0.62  thf('111', plain,
% 0.37/0.62      (((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.37/0.62       ~ ((v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['109', '110'])).
% 0.37/0.62  thf('112', plain, (~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('sat_resolution*', [status(thm)],
% 0.37/0.62                ['1', '3', '66', '68', '69', '70', '73', '111'])).
% 0.37/0.62  thf('113', plain, (~ (v4_tops_1 @ sk_C @ sk_A)),
% 0.37/0.62      inference('simpl_trail', [status(thm)], ['64', '112'])).
% 0.37/0.62  thf('114', plain, (~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['62', '113'])).
% 0.37/0.62  thf('115', plain,
% 0.37/0.62      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['4'])).
% 0.37/0.62  thf('116', plain, ($false),
% 0.37/0.62      inference('sat_resolution*', [status(thm)],
% 0.37/0.62                ['1', '3', '114', '115', '111'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
