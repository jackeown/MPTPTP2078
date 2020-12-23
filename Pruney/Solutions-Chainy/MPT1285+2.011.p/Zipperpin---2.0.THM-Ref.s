%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.09lOryy4JB

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:56 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 273 expanded)
%              Number of leaves         :   24 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          : 1170 (4910 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v6_tops_1 @ X9 @ X10 )
      | ( X9
        = ( k1_tops_1 @ X10 @ ( k2_pre_topc @ X10 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X11 @ X12 ) @ X11 ) ) ),
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

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('25',plain,
    ( ! [X13: $i,X14: $i] :
        ( ~ ( l1_pre_topc @ X13 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( v3_pre_topc @ X14 @ X13 )
        | ( ( k1_tops_1 @ X13 @ X14 )
          = X14 ) )
   <= ! [X13: $i,X14: $i] :
        ( ~ ( l1_pre_topc @ X13 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( v3_pre_topc @ X14 @ X13 )
        | ( ( k1_tops_1 @ X13 @ X14 )
          = X14 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('27',plain,
    ( ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('28',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ! [X13: $i,X14: $i] :
        ( ~ ( l1_pre_topc @ X13 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( v3_pre_topc @ X14 @ X13 )
        | ( ( k1_tops_1 @ X13 @ X14 )
          = X14 ) )
    | ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 ) ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 ) ) ),
    inference(simpl_trail,[status(thm)],['25','33'])).

thf('35',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['22','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) @ X7 )
      | ~ ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ ( k1_tops_1 @ X8 @ X7 ) ) )
      | ( v4_tops_1 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['44','49','50','52'])).

thf('54',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('58',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('59',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('61',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('62',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['62'])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['64'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_tops_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X9
       != ( k1_tops_1 @ X10 @ ( k2_pre_topc @ X10 @ X9 ) ) )
      | ( v6_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('103',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','56','59','60','61','63','65','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.09lOryy4JB
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:19:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 136 iterations in 0.088s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.41/0.61  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.41/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.41/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(t107_tops_1, conjecture,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( l1_pre_topc @ B ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61               ( ![D:$i]:
% 0.41/0.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.61                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.41/0.61                       ( v6_tops_1 @ D @ B ) ) & 
% 0.41/0.61                     ( ( v6_tops_1 @ C @ A ) =>
% 0.41/0.61                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i]:
% 0.41/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61          ( ![B:$i]:
% 0.41/0.61            ( ( l1_pre_topc @ B ) =>
% 0.41/0.61              ( ![C:$i]:
% 0.41/0.61                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61                  ( ![D:$i]:
% 0.41/0.61                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.61                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.41/0.61                          ( v6_tops_1 @ D @ B ) ) & 
% 0.41/0.61                        ( ( v6_tops_1 @ C @ A ) =>
% 0.41/0.61                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.41/0.61  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('split', [status(esa)], ['2'])).
% 0.41/0.61  thf('4', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('split', [status(esa)], ['4'])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d8_tops_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ( v6_tops_1 @ B @ A ) <=>
% 0.41/0.61             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.41/0.61          | ~ (v6_tops_1 @ X9 @ X10)
% 0.41/0.61          | ((X9) = (k1_tops_1 @ X10 @ (k2_pre_topc @ X10 @ X9)))
% 0.41/0.61          | ~ (l1_pre_topc @ X10))),
% 0.41/0.61      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.41/0.61        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.61  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.41/0.61        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.41/0.61         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['5', '10'])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(dt_k2_pre_topc, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.61       ( m1_subset_1 @
% 0.41/0.61         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X3 : $i, X4 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X3)
% 0.41/0.61          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.41/0.61          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.41/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.61  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.61  thf(fc9_tops_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.41/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.61       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X11 : $i, X12 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X11)
% 0.41/0.61          | ~ (v2_pre_topc @ X11)
% 0.41/0.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.41/0.61          | (v3_pre_topc @ (k1_tops_1 @ X11 @ X12) @ X11))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)
% 0.41/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.61  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)),
% 0.41/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['11', '21'])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t55_tops_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( l1_pre_topc @ B ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61               ( ![D:$i]:
% 0.41/0.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.61                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.41/0.61                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.41/0.61                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.41/0.61                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X13)
% 0.41/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.61          | ~ (v3_pre_topc @ X14 @ X13)
% 0.41/0.61          | ((k1_tops_1 @ X13 @ X14) = (X14))
% 0.41/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.61          | ~ (l1_pre_topc @ X16)
% 0.41/0.61          | ~ (v2_pre_topc @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      ((![X13 : $i, X14 : $i]:
% 0.41/0.61          (~ (l1_pre_topc @ X13)
% 0.41/0.61           | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.61           | ~ (v3_pre_topc @ X14 @ X13)
% 0.41/0.61           | ((k1_tops_1 @ X13 @ X14) = (X14))))
% 0.41/0.61         <= ((![X13 : $i, X14 : $i]:
% 0.41/0.61                (~ (l1_pre_topc @ X13)
% 0.41/0.61                 | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.61                 | ~ (v3_pre_topc @ X14 @ X13)
% 0.41/0.61                 | ((k1_tops_1 @ X13 @ X14) = (X14)))))),
% 0.41/0.61      inference('split', [status(esa)], ['24'])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      ((![X15 : $i, X16 : $i]:
% 0.41/0.61          (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.61           | ~ (l1_pre_topc @ X16)
% 0.41/0.61           | ~ (v2_pre_topc @ X16)))
% 0.41/0.61         <= ((![X15 : $i, X16 : $i]:
% 0.41/0.61                (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.61                 | ~ (l1_pre_topc @ X16)
% 0.41/0.61                 | ~ (v2_pre_topc @ X16))))),
% 0.41/0.61      inference('split', [status(esa)], ['24'])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.41/0.61         <= ((![X15 : $i, X16 : $i]:
% 0.41/0.61                (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.61                 | ~ (l1_pre_topc @ X16)
% 0.41/0.61                 | ~ (v2_pre_topc @ X16))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.61  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (~
% 0.41/0.61       (![X15 : $i, X16 : $i]:
% 0.41/0.61          (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.61           | ~ (l1_pre_topc @ X16)
% 0.41/0.61           | ~ (v2_pre_topc @ X16)))),
% 0.41/0.61      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      ((![X13 : $i, X14 : $i]:
% 0.41/0.61          (~ (l1_pre_topc @ X13)
% 0.41/0.61           | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.61           | ~ (v3_pre_topc @ X14 @ X13)
% 0.41/0.61           | ((k1_tops_1 @ X13 @ X14) = (X14)))) | 
% 0.41/0.61       (![X15 : $i, X16 : $i]:
% 0.41/0.61          (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.61           | ~ (l1_pre_topc @ X16)
% 0.41/0.61           | ~ (v2_pre_topc @ X16)))),
% 0.41/0.61      inference('split', [status(esa)], ['24'])).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      ((![X13 : $i, X14 : $i]:
% 0.41/0.61          (~ (l1_pre_topc @ X13)
% 0.41/0.61           | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.61           | ~ (v3_pre_topc @ X14 @ X13)
% 0.41/0.61           | ((k1_tops_1 @ X13 @ X14) = (X14))))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X13)
% 0.41/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.61          | ~ (v3_pre_topc @ X14 @ X13)
% 0.41/0.61          | ((k1_tops_1 @ X13 @ X14) = (X14)))),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['25', '33'])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.41/0.61        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['23', '34'])).
% 0.41/0.61  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['22', '37'])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d6_tops_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ( v4_tops_1 @ B @ A ) <=>
% 0.41/0.61             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.41/0.61               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.41/0.61          | ~ (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 0.41/0.61          | ~ (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ (k1_tops_1 @ X8 @ X7)))
% 0.41/0.61          | (v4_tops_1 @ X7 @ X8)
% 0.41/0.61          | ~ (l1_pre_topc @ X8))),
% 0.41/0.61      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v4_tops_1 @ sk_C @ sk_A)
% 0.41/0.61        | ~ (r1_tarski @ sk_C @ 
% 0.41/0.61             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.41/0.61        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.41/0.61             sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.61  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      (((v4_tops_1 @ sk_C @ sk_A)
% 0.41/0.61        | ~ (r1_tarski @ sk_C @ 
% 0.41/0.61             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.41/0.61        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.41/0.61             sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.41/0.61         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.41/0.61              sk_C)
% 0.41/0.61         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['38', '43'])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t48_pre_topc, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (![X5 : $i, X6 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.41/0.61          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ X5))
% 0.41/0.61          | ~ (l1_pre_topc @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.61  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('49', plain, ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.41/0.61         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['5', '10'])).
% 0.41/0.61  thf(d10_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.61  thf('52', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.61      inference('simplify', [status(thm)], ['51'])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['44', '49', '50', '52'])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.41/0.61        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.41/0.61        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('split', [status(esa)], ['54'])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['53', '55'])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['11', '21'])).
% 0.41/0.61  thf('58', plain,
% 0.41/0.61      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.41/0.61      inference('split', [status(esa)], ['54'])).
% 0.41/0.61  thf('59', plain,
% 0.41/0.61      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.61  thf('60', plain,
% 0.41/0.61      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('split', [status(esa)], ['4'])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.41/0.61       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('split', [status(esa)], ['54'])).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      (((v3_pre_topc @ sk_D @ sk_B)
% 0.41/0.61        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.41/0.61        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.41/0.61       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('split', [status(esa)], ['62'])).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      (((v4_tops_1 @ sk_D @ sk_B)
% 0.41/0.61        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.41/0.61        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.41/0.61       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.41/0.61      inference('split', [status(esa)], ['64'])).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (![X3 : $i, X4 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X3)
% 0.41/0.61          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.41/0.61          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.41/0.61  thf('68', plain,
% 0.41/0.61      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.41/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61        | ~ (l1_pre_topc @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.41/0.61  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['68', '69'])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['62'])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t56_tops_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.41/0.61                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('73', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.61          | ~ (v3_pre_topc @ X17 @ X18)
% 0.41/0.61          | ~ (r1_tarski @ X17 @ X19)
% 0.41/0.61          | (r1_tarski @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.41/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.41/0.61          | ~ (l1_pre_topc @ X18))),
% 0.41/0.61      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.41/0.61          | ~ (r1_tarski @ sk_D @ X0)
% 0.41/0.61          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['72', '73'])).
% 0.41/0.61  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('76', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.41/0.61          | ~ (r1_tarski @ sk_D @ X0)
% 0.41/0.61          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['74', '75'])).
% 0.41/0.61  thf('77', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          (~ (r1_tarski @ sk_D @ X0)
% 0.41/0.61           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.41/0.61           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.41/0.61         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['71', '76'])).
% 0.41/0.61  thf('78', plain,
% 0.41/0.61      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.41/0.61         | ~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.41/0.61         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['70', '77'])).
% 0.41/0.61  thf('79', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('80', plain,
% 0.41/0.61      (![X5 : $i, X6 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.41/0.61          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ X5))
% 0.41/0.61          | ~ (l1_pre_topc @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.41/0.61  thf('81', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_B)
% 0.41/0.61        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['79', '80'])).
% 0.41/0.61  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('83', plain, ((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))),
% 0.41/0.61      inference('demod', [status(thm)], ['81', '82'])).
% 0.41/0.61  thf('84', plain,
% 0.41/0.61      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.41/0.61         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['78', '83'])).
% 0.41/0.61  thf('85', plain,
% 0.41/0.61      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['64'])).
% 0.41/0.61  thf('86', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('87', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.41/0.61          | ~ (v4_tops_1 @ X7 @ X8)
% 0.41/0.61          | (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 0.41/0.61          | ~ (l1_pre_topc @ X8))),
% 0.41/0.61      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.41/0.61  thf('88', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_B)
% 0.41/0.61        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.41/0.61        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['86', '87'])).
% 0.41/0.61  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('90', plain,
% 0.41/0.61      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.41/0.61        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['88', '89'])).
% 0.41/0.61  thf('91', plain,
% 0.41/0.61      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.41/0.61         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['85', '90'])).
% 0.41/0.61  thf('92', plain,
% 0.41/0.61      (![X0 : $i, X2 : $i]:
% 0.41/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.61  thf('93', plain,
% 0.41/0.61      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.41/0.61         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.41/0.61         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['91', '92'])).
% 0.41/0.61  thf('94', plain,
% 0.41/0.61      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.41/0.61         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['84', '93'])).
% 0.41/0.61  thf('95', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('96', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.41/0.61          | ((X9) != (k1_tops_1 @ X10 @ (k2_pre_topc @ X10 @ X9)))
% 0.41/0.61          | (v6_tops_1 @ X9 @ X10)
% 0.41/0.61          | ~ (l1_pre_topc @ X10))),
% 0.41/0.61      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.41/0.61  thf('97', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_B)
% 0.41/0.61        | (v6_tops_1 @ sk_D @ sk_B)
% 0.41/0.61        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['95', '96'])).
% 0.41/0.61  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('99', plain,
% 0.41/0.61      (((v6_tops_1 @ sk_D @ sk_B)
% 0.41/0.61        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.41/0.61      inference('demod', [status(thm)], ['97', '98'])).
% 0.41/0.61  thf('100', plain,
% 0.41/0.61      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.41/0.61         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['94', '99'])).
% 0.41/0.61  thf('101', plain,
% 0.41/0.61      (((v6_tops_1 @ sk_D @ sk_B))
% 0.41/0.61         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['100'])).
% 0.41/0.61  thf('102', plain,
% 0.41/0.61      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['54'])).
% 0.41/0.61  thf('103', plain,
% 0.41/0.61      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.41/0.61       ((v6_tops_1 @ sk_D @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['101', '102'])).
% 0.41/0.61  thf('104', plain, ($false),
% 0.41/0.61      inference('sat_resolution*', [status(thm)],
% 0.41/0.61                ['1', '3', '56', '59', '60', '61', '63', '65', '103'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
