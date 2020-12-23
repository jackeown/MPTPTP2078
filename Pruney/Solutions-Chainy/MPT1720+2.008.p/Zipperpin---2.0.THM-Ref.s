%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tgo9boPW3z

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:29 EST 2020

% Result     : Theorem 49.82s
% Output     : Refutation 49.92s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 447 expanded)
%              Number of leaves         :   32 ( 140 expanded)
%              Depth                    :   33
%              Number of atoms          : 2167 (7979 expanded)
%              Number of equality atoms :   41 (  50 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t29_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( ( m1_pre_topc @ B @ C )
                      & ( m1_pre_topc @ D @ C ) )
                   => ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( ( m1_pre_topc @ B @ C )
                        & ( m1_pre_topc @ D @ C ) )
                     => ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,(
    m1_pre_topc @ sk_D_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ X0 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ X0 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('24',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_D_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf(d2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_pre_topc @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( D
                      = ( k1_tsep_1 @ A @ B @ C ) )
                  <=> ( ( u1_struct_0 @ D )
                      = ( k2_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ( X16
       != ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
      | ( ( u1_struct_0 @ X16 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) @ X15 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_D_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['25','45'])).

thf('47',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['8','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_D_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('61',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( r1_tarski @ ( k2_struct_0 @ X6 ) @ ( k2_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['63','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('84',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('92',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) @ X15 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['83','102'])).

thf('104',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['82','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('107',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ~ ( m1_pre_topc @ sk_D_2 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 )
    | ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ( ( k2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) )
      = ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) )
    | ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('116',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) )
      | ( m1_pre_topc @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X1 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['81','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X0 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['73','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('124',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('125',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_C_1 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ X0 )
      | ( v2_struct_0 @ sk_D_2 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','127'])).

thf('129',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D_2 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_D_2 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_D_2 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['0','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tgo9boPW3z
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:50:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 49.82/50.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 49.82/50.08  % Solved by: fo/fo7.sh
% 49.82/50.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 49.82/50.08  % done 10375 iterations in 49.608s
% 49.82/50.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 49.82/50.08  % SZS output start Refutation
% 49.82/50.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 49.82/50.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 49.82/50.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 49.82/50.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 49.82/50.08  thf(sk_C_1_type, type, sk_C_1: $i).
% 49.82/50.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 49.82/50.08  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 49.82/50.08  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 49.82/50.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 49.82/50.08  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 49.82/50.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 49.82/50.08  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 49.82/50.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 49.82/50.08  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 49.82/50.08  thf(sk_B_type, type, sk_B: $i).
% 49.82/50.08  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 49.82/50.08  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 49.82/50.08  thf(sk_D_2_type, type, sk_D_2: $i).
% 49.82/50.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 49.82/50.08  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 49.82/50.08  thf(sk_A_type, type, sk_A: $i).
% 49.82/50.08  thf(t29_tmap_1, conjecture,
% 49.82/50.08    (![A:$i]:
% 49.82/50.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.82/50.08       ( ![B:$i]:
% 49.82/50.08         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 49.82/50.08           ( ![C:$i]:
% 49.82/50.08             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 49.82/50.08               ( ![D:$i]:
% 49.82/50.08                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 49.82/50.08                   ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 49.82/50.08                     ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ))).
% 49.82/50.08  thf(zf_stmt_0, negated_conjecture,
% 49.82/50.08    (~( ![A:$i]:
% 49.82/50.08        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 49.82/50.08            ( l1_pre_topc @ A ) ) =>
% 49.82/50.08          ( ![B:$i]:
% 49.82/50.08            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 49.82/50.08              ( ![C:$i]:
% 49.82/50.08                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 49.82/50.08                  ( ![D:$i]:
% 49.82/50.08                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 49.82/50.08                      ( ( ( m1_pre_topc @ B @ C ) & ( m1_pre_topc @ D @ C ) ) =>
% 49.82/50.08                        ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ D ) @ C ) ) ) ) ) ) ) ) ) )),
% 49.82/50.08    inference('cnf.neg', [status(esa)], [t29_tmap_1])).
% 49.82/50.08  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('1', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf(dt_k1_tsep_1, axiom,
% 49.82/50.08    (![A:$i,B:$i,C:$i]:
% 49.82/50.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 49.82/50.08         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 49.82/50.08         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 49.82/50.08       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 49.82/50.08         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 49.82/50.08         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 49.82/50.08  thf('3', plain,
% 49.82/50.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X18 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X18)
% 49.82/50.08          | ~ (l1_pre_topc @ X19)
% 49.82/50.08          | (v2_struct_0 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X20)
% 49.82/50.08          | ~ (m1_pre_topc @ X20 @ X19)
% 49.82/50.08          | (m1_pre_topc @ (k1_tsep_1 @ X19 @ X18 @ X20) @ X19))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.82/50.08  thf('4', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ X0)
% 49.82/50.08          | (v2_struct_0 @ sk_A)
% 49.82/50.08          | ~ (l1_pre_topc @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('sup-', [status(thm)], ['2', '3'])).
% 49.82/50.08  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('6', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ X0)
% 49.82/50.08          | (v2_struct_0 @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('demod', [status(thm)], ['4', '5'])).
% 49.82/50.08  thf('7', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_A))),
% 49.82/50.08      inference('sup-', [status(thm)], ['1', '6'])).
% 49.82/50.08  thf(d3_struct_0, axiom,
% 49.82/50.08    (![A:$i]:
% 49.82/50.08     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 49.82/50.08  thf('8', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 49.82/50.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 49.82/50.08  thf('9', plain, ((m1_pre_topc @ sk_D_2 @ sk_C_1)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('11', plain,
% 49.82/50.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X18 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X18)
% 49.82/50.08          | ~ (l1_pre_topc @ X19)
% 49.82/50.08          | (v2_struct_0 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X20)
% 49.82/50.08          | ~ (m1_pre_topc @ X20 @ X19)
% 49.82/50.08          | (m1_pre_topc @ (k1_tsep_1 @ X19 @ X18 @ X20) @ X19))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.82/50.08  thf('12', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ X0) @ sk_C_1)
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 49.82/50.08          | (v2_struct_0 @ X0)
% 49.82/50.08          | (v2_struct_0 @ sk_C_1)
% 49.82/50.08          | ~ (l1_pre_topc @ sk_C_1)
% 49.82/50.08          | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('sup-', [status(thm)], ['10', '11'])).
% 49.82/50.08  thf('13', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf(dt_m1_pre_topc, axiom,
% 49.82/50.08    (![A:$i]:
% 49.82/50.08     ( ( l1_pre_topc @ A ) =>
% 49.82/50.08       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 49.82/50.08  thf('14', plain,
% 49.82/50.08      (![X12 : $i, X13 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X12 @ X13)
% 49.82/50.08          | (l1_pre_topc @ X12)
% 49.82/50.08          | ~ (l1_pre_topc @ X13))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.82/50.08  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 49.82/50.08      inference('sup-', [status(thm)], ['13', '14'])).
% 49.82/50.08  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 49.82/50.08      inference('demod', [status(thm)], ['15', '16'])).
% 49.82/50.08  thf('18', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         ((m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ X0) @ sk_C_1)
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 49.82/50.08          | (v2_struct_0 @ X0)
% 49.82/50.08          | (v2_struct_0 @ sk_C_1)
% 49.82/50.08          | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('demod', [status(thm)], ['12', '17'])).
% 49.82/50.08  thf('19', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2) @ sk_C_1))),
% 49.82/50.08      inference('sup-', [status(thm)], ['9', '18'])).
% 49.82/50.08  thf('20', plain,
% 49.82/50.08      (![X12 : $i, X13 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X12 @ X13)
% 49.82/50.08          | (l1_pre_topc @ X12)
% 49.82/50.08          | ~ (l1_pre_topc @ X13))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.82/50.08  thf('21', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | ~ (l1_pre_topc @ sk_C_1)
% 49.82/50.08        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup-', [status(thm)], ['19', '20'])).
% 49.82/50.08  thf('22', plain, ((l1_pre_topc @ sk_C_1)),
% 49.82/50.08      inference('demod', [status(thm)], ['15', '16'])).
% 49.82/50.08  thf('23', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('demod', [status(thm)], ['21', '22'])).
% 49.82/50.08  thf(dt_l1_pre_topc, axiom,
% 49.82/50.08    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 49.82/50.08  thf('24', plain,
% 49.82/50.08      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 49.82/50.08  thf('25', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup-', [status(thm)], ['23', '24'])).
% 49.82/50.08  thf('26', plain, ((m1_pre_topc @ sk_D_2 @ sk_C_1)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('28', plain,
% 49.82/50.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X18 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X18)
% 49.82/50.08          | ~ (l1_pre_topc @ X19)
% 49.82/50.08          | (v2_struct_0 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X20)
% 49.82/50.08          | ~ (m1_pre_topc @ X20 @ X19)
% 49.82/50.08          | (v1_pre_topc @ (k1_tsep_1 @ X19 @ X18 @ X20)))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.82/50.08  thf('29', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ X0))
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 49.82/50.08          | (v2_struct_0 @ X0)
% 49.82/50.08          | (v2_struct_0 @ sk_C_1)
% 49.82/50.08          | ~ (l1_pre_topc @ sk_C_1)
% 49.82/50.08          | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('sup-', [status(thm)], ['27', '28'])).
% 49.82/50.08  thf('30', plain, ((l1_pre_topc @ sk_C_1)),
% 49.82/50.08      inference('demod', [status(thm)], ['15', '16'])).
% 49.82/50.08  thf('31', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         ((v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ X0))
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ sk_C_1)
% 49.82/50.08          | (v2_struct_0 @ X0)
% 49.82/50.08          | (v2_struct_0 @ sk_C_1)
% 49.82/50.08          | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('demod', [status(thm)], ['29', '30'])).
% 49.82/50.08  thf('32', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup-', [status(thm)], ['26', '31'])).
% 49.82/50.08  thf('33', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2) @ sk_C_1))),
% 49.82/50.08      inference('sup-', [status(thm)], ['9', '18'])).
% 49.82/50.08  thf(d2_tsep_1, axiom,
% 49.82/50.08    (![A:$i]:
% 49.82/50.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 49.82/50.08       ( ![B:$i]:
% 49.82/50.08         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 49.82/50.08           ( ![C:$i]:
% 49.82/50.08             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 49.82/50.08               ( ![D:$i]:
% 49.82/50.08                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 49.82/50.08                     ( m1_pre_topc @ D @ A ) ) =>
% 49.82/50.08                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 49.82/50.08                     ( ( u1_struct_0 @ D ) =
% 49.82/50.08                       ( k2_xboole_0 @
% 49.82/50.08                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 49.82/50.08  thf('34', plain,
% 49.82/50.08      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 49.82/50.08         ((v2_struct_0 @ X14)
% 49.82/50.08          | ~ (m1_pre_topc @ X14 @ X15)
% 49.82/50.08          | (v2_struct_0 @ X16)
% 49.82/50.08          | ~ (v1_pre_topc @ X16)
% 49.82/50.08          | ~ (m1_pre_topc @ X16 @ X15)
% 49.82/50.08          | ((X16) != (k1_tsep_1 @ X15 @ X14 @ X17))
% 49.82/50.08          | ((u1_struct_0 @ X16)
% 49.82/50.08              = (k2_xboole_0 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17)))
% 49.82/50.08          | ~ (m1_pre_topc @ X17 @ X15)
% 49.82/50.08          | (v2_struct_0 @ X17)
% 49.82/50.08          | ~ (l1_pre_topc @ X15)
% 49.82/50.08          | (v2_struct_0 @ X15))),
% 49.82/50.08      inference('cnf', [status(esa)], [d2_tsep_1])).
% 49.82/50.08  thf('35', plain,
% 49.82/50.08      (![X14 : $i, X15 : $i, X17 : $i]:
% 49.82/50.08         ((v2_struct_0 @ X15)
% 49.82/50.08          | ~ (l1_pre_topc @ X15)
% 49.82/50.08          | (v2_struct_0 @ X17)
% 49.82/50.08          | ~ (m1_pre_topc @ X17 @ X15)
% 49.82/50.08          | ((u1_struct_0 @ (k1_tsep_1 @ X15 @ X14 @ X17))
% 49.82/50.08              = (k2_xboole_0 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17)))
% 49.82/50.08          | ~ (m1_pre_topc @ (k1_tsep_1 @ X15 @ X14 @ X17) @ X15)
% 49.82/50.08          | ~ (v1_pre_topc @ (k1_tsep_1 @ X15 @ X14 @ X17))
% 49.82/50.08          | (v2_struct_0 @ (k1_tsep_1 @ X15 @ X14 @ X17))
% 49.82/50.08          | ~ (m1_pre_topc @ X14 @ X15)
% 49.82/50.08          | (v2_struct_0 @ X14))),
% 49.82/50.08      inference('simplify', [status(thm)], ['34'])).
% 49.82/50.08  thf('36', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | ~ (m1_pre_topc @ sk_B @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | ~ (m1_pre_topc @ sk_D_2 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | ~ (l1_pre_topc @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1))),
% 49.82/50.08      inference('sup-', [status(thm)], ['33', '35'])).
% 49.82/50.08  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('38', plain, ((m1_pre_topc @ sk_D_2 @ sk_C_1)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('39', plain, ((l1_pre_topc @ sk_C_1)),
% 49.82/50.08      inference('demod', [status(thm)], ['15', '16'])).
% 49.82/50.08  thf('40', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1))),
% 49.82/50.08      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 49.82/50.08  thf('41', plain,
% 49.82/50.08      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2))),
% 49.82/50.08      inference('simplify', [status(thm)], ['40'])).
% 49.82/50.08  thf('42', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | ((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2))))),
% 49.82/50.08      inference('sup-', [status(thm)], ['32', '41'])).
% 49.82/50.08  thf('43', plain,
% 49.82/50.08      ((((u1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2))),
% 49.82/50.08      inference('simplify', [status(thm)], ['42'])).
% 49.82/50.08  thf('44', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 49.82/50.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 49.82/50.08  thf('45', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup+', [status(thm)], ['43', '44'])).
% 49.82/50.08  thf('46', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2))))),
% 49.82/50.08      inference('sup-', [status(thm)], ['25', '45'])).
% 49.82/50.08  thf('47', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2))),
% 49.82/50.08      inference('simplify', [status(thm)], ['46'])).
% 49.82/50.08  thf('48', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | ~ (l1_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup+', [status(thm)], ['8', '47'])).
% 49.82/50.08  thf('49', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('50', plain,
% 49.82/50.08      (![X12 : $i, X13 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X12 @ X13)
% 49.82/50.08          | (l1_pre_topc @ X12)
% 49.82/50.08          | ~ (l1_pre_topc @ X13))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.82/50.08  thf('51', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 49.82/50.08      inference('sup-', [status(thm)], ['49', '50'])).
% 49.82/50.08  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 49.82/50.08      inference('demod', [status(thm)], ['51', '52'])).
% 49.82/50.08  thf('54', plain,
% 49.82/50.08      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 49.82/50.08  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 49.82/50.08      inference('sup-', [status(thm)], ['53', '54'])).
% 49.82/50.08  thf('56', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('demod', [status(thm)], ['48', '55'])).
% 49.82/50.08  thf('57', plain,
% 49.82/50.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X18 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X18)
% 49.82/50.08          | ~ (l1_pre_topc @ X19)
% 49.82/50.08          | (v2_struct_0 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X20)
% 49.82/50.08          | ~ (m1_pre_topc @ X20 @ X19)
% 49.82/50.08          | ~ (v2_struct_0 @ (k1_tsep_1 @ X19 @ X18 @ X20)))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.82/50.08  thf('58', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | ~ (m1_pre_topc @ sk_D_2 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | ~ (l1_pre_topc @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | ~ (m1_pre_topc @ sk_B @ sk_C_1))),
% 49.82/50.08      inference('sup-', [status(thm)], ['56', '57'])).
% 49.82/50.08  thf('59', plain, ((m1_pre_topc @ sk_D_2 @ sk_C_1)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('60', plain, ((l1_pre_topc @ sk_C_1)),
% 49.82/50.08      inference('demod', [status(thm)], ['15', '16'])).
% 49.82/50.08  thf('61', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('62', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | ((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 49.82/50.08  thf('63', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('simplify', [status(thm)], ['62'])).
% 49.82/50.08  thf('64', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('demod', [status(thm)], ['21', '22'])).
% 49.82/50.08  thf('65', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (m1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2) @ sk_C_1))),
% 49.82/50.08      inference('sup-', [status(thm)], ['9', '18'])).
% 49.82/50.08  thf(d9_pre_topc, axiom,
% 49.82/50.08    (![A:$i]:
% 49.82/50.08     ( ( l1_pre_topc @ A ) =>
% 49.82/50.08       ( ![B:$i]:
% 49.82/50.08         ( ( l1_pre_topc @ B ) =>
% 49.82/50.08           ( ( m1_pre_topc @ B @ A ) <=>
% 49.82/50.08             ( ( ![C:$i]:
% 49.82/50.08                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 49.82/50.08                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 49.82/50.08                     ( ?[D:$i]:
% 49.82/50.08                       ( ( m1_subset_1 @
% 49.82/50.08                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 49.82/50.08                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 49.82/50.08                         ( ( C ) =
% 49.82/50.08                           ( k9_subset_1 @
% 49.82/50.08                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 49.82/50.08               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 49.82/50.08  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 49.82/50.08  thf(zf_stmt_2, axiom,
% 49.82/50.08    (![D:$i,C:$i,B:$i,A:$i]:
% 49.82/50.08     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 49.82/50.08       ( ( ( C ) =
% 49.82/50.08           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 49.82/50.08         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 49.82/50.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 49.82/50.08  thf(zf_stmt_3, axiom,
% 49.82/50.08    (![A:$i]:
% 49.82/50.08     ( ( l1_pre_topc @ A ) =>
% 49.82/50.08       ( ![B:$i]:
% 49.82/50.08         ( ( l1_pre_topc @ B ) =>
% 49.82/50.08           ( ( m1_pre_topc @ B @ A ) <=>
% 49.82/50.08             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 49.82/50.08               ( ![C:$i]:
% 49.82/50.08                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 49.82/50.08                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 49.82/50.08                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 49.82/50.08  thf('66', plain,
% 49.82/50.08      (![X6 : $i, X7 : $i]:
% 49.82/50.08         (~ (l1_pre_topc @ X6)
% 49.82/50.08          | ~ (m1_pre_topc @ X6 @ X7)
% 49.82/50.08          | (r1_tarski @ (k2_struct_0 @ X6) @ (k2_struct_0 @ X7))
% 49.82/50.08          | ~ (l1_pre_topc @ X7))),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 49.82/50.08  thf('67', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | ~ (l1_pre_topc @ sk_C_1)
% 49.82/50.08        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)) @ 
% 49.82/50.08           (k2_struct_0 @ sk_C_1))
% 49.82/50.08        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup-', [status(thm)], ['65', '66'])).
% 49.82/50.08  thf('68', plain, ((l1_pre_topc @ sk_C_1)),
% 49.82/50.08      inference('demod', [status(thm)], ['15', '16'])).
% 49.82/50.08  thf('69', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)) @ 
% 49.82/50.08           (k2_struct_0 @ sk_C_1))
% 49.82/50.08        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('demod', [status(thm)], ['67', '68'])).
% 49.82/50.08  thf('70', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)) @ 
% 49.82/50.08           (k2_struct_0 @ sk_C_1))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2))),
% 49.82/50.08      inference('sup-', [status(thm)], ['64', '69'])).
% 49.82/50.08  thf('71', plain,
% 49.82/50.08      (((r1_tarski @ (k2_struct_0 @ (k1_tsep_1 @ sk_C_1 @ sk_B @ sk_D_2)) @ 
% 49.82/50.08         (k2_struct_0 @ sk_C_1))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('simplify', [status(thm)], ['70'])).
% 49.82/50.08  thf('72', plain,
% 49.82/50.08      (((r1_tarski @ 
% 49.82/50.08         (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)) @ 
% 49.82/50.08         (k2_struct_0 @ sk_C_1))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2))),
% 49.82/50.08      inference('sup+', [status(thm)], ['63', '71'])).
% 49.82/50.08  thf('73', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_C_1)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (r1_tarski @ 
% 49.82/50.08           (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)) @ 
% 49.82/50.08           (k2_struct_0 @ sk_C_1)))),
% 49.82/50.08      inference('simplify', [status(thm)], ['72'])).
% 49.82/50.08  thf('74', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 49.82/50.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 49.82/50.08  thf('75', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_A))),
% 49.82/50.08      inference('sup-', [status(thm)], ['1', '6'])).
% 49.82/50.08  thf('76', plain,
% 49.82/50.08      (![X12 : $i, X13 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X12 @ X13)
% 49.82/50.08          | (l1_pre_topc @ X12)
% 49.82/50.08          | ~ (l1_pre_topc @ X13))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.82/50.08  thf('77', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | ~ (l1_pre_topc @ sk_A)
% 49.82/50.08        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup-', [status(thm)], ['75', '76'])).
% 49.82/50.08  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('79', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('demod', [status(thm)], ['77', '78'])).
% 49.82/50.08  thf('80', plain,
% 49.82/50.08      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 49.82/50.08  thf('81', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup-', [status(thm)], ['79', '80'])).
% 49.82/50.08  thf('82', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 49.82/50.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 49.82/50.08  thf('83', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup-', [status(thm)], ['79', '80'])).
% 49.82/50.08  thf('84', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('85', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('86', plain,
% 49.82/50.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X18 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X18)
% 49.82/50.08          | ~ (l1_pre_topc @ X19)
% 49.82/50.08          | (v2_struct_0 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X20)
% 49.82/50.08          | ~ (m1_pre_topc @ X20 @ X19)
% 49.82/50.08          | (v1_pre_topc @ (k1_tsep_1 @ X19 @ X18 @ X20)))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.82/50.08  thf('87', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ X0)
% 49.82/50.08          | (v2_struct_0 @ sk_A)
% 49.82/50.08          | ~ (l1_pre_topc @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('sup-', [status(thm)], ['85', '86'])).
% 49.82/50.08  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('89', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ X0)
% 49.82/50.08          | (v2_struct_0 @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('demod', [status(thm)], ['87', '88'])).
% 49.82/50.08  thf('90', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup-', [status(thm)], ['84', '89'])).
% 49.82/50.08  thf('91', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_A))),
% 49.82/50.08      inference('sup-', [status(thm)], ['1', '6'])).
% 49.82/50.08  thf('92', plain,
% 49.82/50.08      (![X14 : $i, X15 : $i, X17 : $i]:
% 49.82/50.08         ((v2_struct_0 @ X15)
% 49.82/50.08          | ~ (l1_pre_topc @ X15)
% 49.82/50.08          | (v2_struct_0 @ X17)
% 49.82/50.08          | ~ (m1_pre_topc @ X17 @ X15)
% 49.82/50.08          | ((u1_struct_0 @ (k1_tsep_1 @ X15 @ X14 @ X17))
% 49.82/50.08              = (k2_xboole_0 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17)))
% 49.82/50.08          | ~ (m1_pre_topc @ (k1_tsep_1 @ X15 @ X14 @ X17) @ X15)
% 49.82/50.08          | ~ (v1_pre_topc @ (k1_tsep_1 @ X15 @ X14 @ X17))
% 49.82/50.08          | (v2_struct_0 @ (k1_tsep_1 @ X15 @ X14 @ X17))
% 49.82/50.08          | ~ (m1_pre_topc @ X14 @ X15)
% 49.82/50.08          | (v2_struct_0 @ X14))),
% 49.82/50.08      inference('simplify', [status(thm)], ['34'])).
% 49.82/50.08  thf('93', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | ~ (m1_pre_topc @ sk_D_2 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | ~ (l1_pre_topc @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_A))),
% 49.82/50.08      inference('sup-', [status(thm)], ['91', '92'])).
% 49.82/50.08  thf('94', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('95', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('97', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A))),
% 49.82/50.08      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 49.82/50.08  thf('98', plain,
% 49.82/50.08      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2))),
% 49.82/50.08      inference('simplify', [status(thm)], ['97'])).
% 49.82/50.08  thf('99', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2))))),
% 49.82/50.08      inference('sup-', [status(thm)], ['90', '98'])).
% 49.82/50.08  thf('100', plain,
% 49.82/50.08      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2))),
% 49.82/50.08      inference('simplify', [status(thm)], ['99'])).
% 49.82/50.08  thf('101', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 49.82/50.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 49.82/50.08  thf('102', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup+', [status(thm)], ['100', '101'])).
% 49.82/50.08  thf('103', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | ((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2))))),
% 49.82/50.08      inference('sup-', [status(thm)], ['83', '102'])).
% 49.82/50.08  thf('104', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2))),
% 49.82/50.08      inference('simplify', [status(thm)], ['103'])).
% 49.82/50.08  thf('105', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | ~ (l1_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup+', [status(thm)], ['82', '104'])).
% 49.82/50.08  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 49.82/50.08      inference('sup-', [status(thm)], ['53', '54'])).
% 49.82/50.08  thf('107', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('demod', [status(thm)], ['105', '106'])).
% 49.82/50.08  thf('108', plain,
% 49.82/50.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X18 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X18)
% 49.82/50.08          | ~ (l1_pre_topc @ X19)
% 49.82/50.08          | (v2_struct_0 @ X19)
% 49.82/50.08          | (v2_struct_0 @ X20)
% 49.82/50.08          | ~ (m1_pre_topc @ X20 @ X19)
% 49.82/50.08          | ~ (v2_struct_0 @ (k1_tsep_1 @ X19 @ X18 @ X20)))),
% 49.82/50.08      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 49.82/50.08  thf('109', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | ((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | ~ (m1_pre_topc @ sk_D_2 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | ~ (l1_pre_topc @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B)
% 49.82/50.08        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 49.82/50.08      inference('sup-', [status(thm)], ['107', '108'])).
% 49.82/50.08  thf('110', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('112', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.82/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.82/50.08  thf('113', plain,
% 49.82/50.08      (((v2_struct_0 @ sk_B)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | ((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08            = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 49.82/50.08  thf('114', plain,
% 49.82/50.08      ((((k2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2))
% 49.82/50.08          = (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 49.82/50.08        | (v2_struct_0 @ sk_D_2)
% 49.82/50.08        | (v2_struct_0 @ sk_A)
% 49.82/50.08        | (v2_struct_0 @ sk_B))),
% 49.82/50.08      inference('simplify', [status(thm)], ['113'])).
% 49.82/50.08  thf('115', plain,
% 49.82/50.08      (![X0 : $i]:
% 49.82/50.08         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 49.82/50.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 49.82/50.08  thf(t4_tsep_1, axiom,
% 49.82/50.08    (![A:$i]:
% 49.82/50.08     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.82/50.08       ( ![B:$i]:
% 49.82/50.08         ( ( m1_pre_topc @ B @ A ) =>
% 49.82/50.08           ( ![C:$i]:
% 49.82/50.08             ( ( m1_pre_topc @ C @ A ) =>
% 49.82/50.08               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 49.82/50.08                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 49.82/50.08  thf('116', plain,
% 49.82/50.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 49.82/50.08         (~ (m1_pre_topc @ X21 @ X22)
% 49.82/50.08          | ~ (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23))
% 49.82/50.08          | (m1_pre_topc @ X21 @ X23)
% 49.82/50.08          | ~ (m1_pre_topc @ X23 @ X22)
% 49.82/50.08          | ~ (l1_pre_topc @ X22)
% 49.82/50.08          | ~ (v2_pre_topc @ X22))),
% 49.82/50.08      inference('cnf', [status(esa)], [t4_tsep_1])).
% 49.82/50.08  thf('117', plain,
% 49.82/50.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.82/50.08         (~ (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 49.82/50.08          | ~ (l1_struct_0 @ X0)
% 49.82/50.08          | ~ (v2_pre_topc @ X2)
% 49.82/50.08          | ~ (l1_pre_topc @ X2)
% 49.82/50.08          | ~ (m1_pre_topc @ X1 @ X2)
% 49.82/50.08          | (m1_pre_topc @ X0 @ X1)
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ X2))),
% 49.82/50.08      inference('sup-', [status(thm)], ['115', '116'])).
% 49.82/50.08  thf('118', plain,
% 49.82/50.08      (![X0 : $i, X1 : $i]:
% 49.82/50.08         (~ (r1_tarski @ 
% 49.82/50.08             (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)) @ 
% 49.82/50.08             (u1_struct_0 @ X0))
% 49.82/50.08          | (v2_struct_0 @ sk_B)
% 49.82/50.08          | (v2_struct_0 @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ sk_D_2)
% 49.82/50.08          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X1)
% 49.82/50.08          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X0)
% 49.82/50.08          | ~ (m1_pre_topc @ X0 @ X1)
% 49.82/50.08          | ~ (l1_pre_topc @ X1)
% 49.82/50.08          | ~ (v2_pre_topc @ X1)
% 49.82/50.08          | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2)))),
% 49.82/50.08      inference('sup-', [status(thm)], ['114', '117'])).
% 49.82/50.08  thf('119', plain,
% 49.82/50.08      (![X0 : $i, X1 : $i]:
% 49.82/50.08         ((v2_struct_0 @ sk_D_2)
% 49.82/50.08          | (v2_struct_0 @ sk_A)
% 49.82/50.08          | (v2_struct_0 @ sk_B)
% 49.82/50.08          | ~ (v2_pre_topc @ X0)
% 49.82/50.08          | ~ (l1_pre_topc @ X0)
% 49.82/50.08          | ~ (m1_pre_topc @ X1 @ X0)
% 49.82/50.08          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X1)
% 49.82/50.08          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X0)
% 49.82/50.08          | (v2_struct_0 @ sk_D_2)
% 49.82/50.08          | (v2_struct_0 @ sk_A)
% 49.92/50.08          | (v2_struct_0 @ sk_B)
% 49.92/50.08          | ~ (r1_tarski @ 
% 49.92/50.08               (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)) @ 
% 49.92/50.08               (u1_struct_0 @ X1)))),
% 49.92/50.08      inference('sup-', [status(thm)], ['81', '118'])).
% 49.92/50.08  thf('120', plain,
% 49.92/50.08      (![X0 : $i, X1 : $i]:
% 49.92/50.08         (~ (r1_tarski @ 
% 49.92/50.08             (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)) @ 
% 49.92/50.08             (u1_struct_0 @ X1))
% 49.92/50.08          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X0)
% 49.92/50.08          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X1)
% 49.92/50.08          | ~ (m1_pre_topc @ X1 @ X0)
% 49.92/50.08          | ~ (l1_pre_topc @ X0)
% 49.92/50.08          | ~ (v2_pre_topc @ X0)
% 49.92/50.08          | (v2_struct_0 @ sk_B)
% 49.92/50.08          | (v2_struct_0 @ sk_A)
% 49.92/50.08          | (v2_struct_0 @ sk_D_2))),
% 49.92/50.08      inference('simplify', [status(thm)], ['119'])).
% 49.92/50.08  thf('121', plain,
% 49.92/50.08      (![X0 : $i, X1 : $i]:
% 49.92/50.08         (~ (r1_tarski @ 
% 49.92/50.08             (k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)) @ 
% 49.92/50.08             (k2_struct_0 @ X0))
% 49.92/50.08          | ~ (l1_struct_0 @ X0)
% 49.92/50.08          | (v2_struct_0 @ sk_D_2)
% 49.92/50.08          | (v2_struct_0 @ sk_A)
% 49.92/50.08          | (v2_struct_0 @ sk_B)
% 49.92/50.08          | ~ (v2_pre_topc @ X1)
% 49.92/50.08          | ~ (l1_pre_topc @ X1)
% 49.92/50.08          | ~ (m1_pre_topc @ X0 @ X1)
% 49.92/50.08          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X0)
% 49.92/50.08          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X1))),
% 49.92/50.08      inference('sup-', [status(thm)], ['74', '120'])).
% 49.92/50.08  thf('122', plain,
% 49.92/50.08      (![X0 : $i]:
% 49.92/50.08         ((v2_struct_0 @ sk_B)
% 49.92/50.08          | (v2_struct_0 @ sk_C_1)
% 49.92/50.08          | (v2_struct_0 @ sk_D_2)
% 49.92/50.08          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X0)
% 49.92/50.08          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_C_1)
% 49.92/50.08          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 49.92/50.08          | ~ (l1_pre_topc @ X0)
% 49.92/50.08          | ~ (v2_pre_topc @ X0)
% 49.92/50.08          | (v2_struct_0 @ sk_B)
% 49.92/50.08          | (v2_struct_0 @ sk_A)
% 49.92/50.08          | (v2_struct_0 @ sk_D_2)
% 49.92/50.08          | ~ (l1_struct_0 @ sk_C_1))),
% 49.92/50.08      inference('sup-', [status(thm)], ['73', '121'])).
% 49.92/50.08  thf('123', plain, ((l1_pre_topc @ sk_C_1)),
% 49.92/50.08      inference('demod', [status(thm)], ['15', '16'])).
% 49.92/50.08  thf('124', plain,
% 49.92/50.08      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 49.92/50.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 49.92/50.08  thf('125', plain, ((l1_struct_0 @ sk_C_1)),
% 49.92/50.08      inference('sup-', [status(thm)], ['123', '124'])).
% 49.92/50.08  thf('126', plain,
% 49.92/50.08      (![X0 : $i]:
% 49.92/50.08         ((v2_struct_0 @ sk_B)
% 49.92/50.08          | (v2_struct_0 @ sk_C_1)
% 49.92/50.08          | (v2_struct_0 @ sk_D_2)
% 49.92/50.08          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X0)
% 49.92/50.08          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_C_1)
% 49.92/50.08          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 49.92/50.08          | ~ (l1_pre_topc @ X0)
% 49.92/50.08          | ~ (v2_pre_topc @ X0)
% 49.92/50.08          | (v2_struct_0 @ sk_B)
% 49.92/50.08          | (v2_struct_0 @ sk_A)
% 49.92/50.08          | (v2_struct_0 @ sk_D_2))),
% 49.92/50.08      inference('demod', [status(thm)], ['122', '125'])).
% 49.92/50.08  thf('127', plain,
% 49.92/50.08      (![X0 : $i]:
% 49.92/50.08         ((v2_struct_0 @ sk_A)
% 49.92/50.08          | ~ (v2_pre_topc @ X0)
% 49.92/50.08          | ~ (l1_pre_topc @ X0)
% 49.92/50.08          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 49.92/50.08          | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_C_1)
% 49.92/50.08          | ~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ X0)
% 49.92/50.08          | (v2_struct_0 @ sk_D_2)
% 49.92/50.08          | (v2_struct_0 @ sk_C_1)
% 49.92/50.08          | (v2_struct_0 @ sk_B))),
% 49.92/50.08      inference('simplify', [status(thm)], ['126'])).
% 49.92/50.08  thf('128', plain,
% 49.92/50.08      (((v2_struct_0 @ sk_D_2)
% 49.92/50.08        | (v2_struct_0 @ sk_A)
% 49.92/50.08        | (v2_struct_0 @ sk_B)
% 49.92/50.08        | (v2_struct_0 @ sk_B)
% 49.92/50.08        | (v2_struct_0 @ sk_C_1)
% 49.92/50.08        | (v2_struct_0 @ sk_D_2)
% 49.92/50.08        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_C_1)
% 49.92/50.08        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 49.92/50.08        | ~ (l1_pre_topc @ sk_A)
% 49.92/50.08        | ~ (v2_pre_topc @ sk_A)
% 49.92/50.08        | (v2_struct_0 @ sk_A))),
% 49.92/50.08      inference('sup-', [status(thm)], ['7', '127'])).
% 49.92/50.08  thf('129', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 49.92/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.92/50.08  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 49.92/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.92/50.08  thf('131', plain, ((v2_pre_topc @ sk_A)),
% 49.92/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.92/50.08  thf('132', plain,
% 49.92/50.08      (((v2_struct_0 @ sk_D_2)
% 49.92/50.08        | (v2_struct_0 @ sk_A)
% 49.92/50.08        | (v2_struct_0 @ sk_B)
% 49.92/50.08        | (v2_struct_0 @ sk_B)
% 49.92/50.08        | (v2_struct_0 @ sk_C_1)
% 49.92/50.08        | (v2_struct_0 @ sk_D_2)
% 49.92/50.08        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_C_1)
% 49.92/50.08        | (v2_struct_0 @ sk_A))),
% 49.92/50.08      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 49.92/50.08  thf('133', plain,
% 49.92/50.08      (((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_C_1)
% 49.92/50.08        | (v2_struct_0 @ sk_C_1)
% 49.92/50.08        | (v2_struct_0 @ sk_B)
% 49.92/50.08        | (v2_struct_0 @ sk_A)
% 49.92/50.08        | (v2_struct_0 @ sk_D_2))),
% 49.92/50.08      inference('simplify', [status(thm)], ['132'])).
% 49.92/50.08  thf('134', plain,
% 49.92/50.08      (~ (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_D_2) @ sk_C_1)),
% 49.92/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.92/50.08  thf('135', plain,
% 49.92/50.08      (((v2_struct_0 @ sk_D_2)
% 49.92/50.08        | (v2_struct_0 @ sk_A)
% 49.92/50.08        | (v2_struct_0 @ sk_B)
% 49.92/50.08        | (v2_struct_0 @ sk_C_1))),
% 49.92/50.08      inference('sup-', [status(thm)], ['133', '134'])).
% 49.92/50.08  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 49.92/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.92/50.08  thf('137', plain,
% 49.92/50.08      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_2))),
% 49.92/50.08      inference('sup-', [status(thm)], ['135', '136'])).
% 49.92/50.08  thf('138', plain, (~ (v2_struct_0 @ sk_C_1)),
% 49.92/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.92/50.08  thf('139', plain, (((v2_struct_0 @ sk_D_2) | (v2_struct_0 @ sk_B))),
% 49.92/50.08      inference('clc', [status(thm)], ['137', '138'])).
% 49.92/50.08  thf('140', plain, (~ (v2_struct_0 @ sk_D_2)),
% 49.92/50.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.92/50.08  thf('141', plain, ((v2_struct_0 @ sk_B)),
% 49.92/50.08      inference('clc', [status(thm)], ['139', '140'])).
% 49.92/50.08  thf('142', plain, ($false), inference('demod', [status(thm)], ['0', '141'])).
% 49.92/50.08  
% 49.92/50.08  % SZS output end Refutation
% 49.92/50.08  
% 49.92/50.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
