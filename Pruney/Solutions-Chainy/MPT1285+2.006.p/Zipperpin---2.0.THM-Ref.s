%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BzoR7Os1sU

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:55 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 309 expanded)
%              Number of leaves         :   25 (  93 expanded)
%              Depth                    :   16
%              Number of atoms          : 1207 (5445 expanded)
%              Number of equality atoms :   17 (  38 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ X8 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v6_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v6_tops_1 @ X12 @ X13 )
      | ( X12
        = ( k1_tops_1 @ X13 @ ( k2_pre_topc @ X13 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('32',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['29','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) )
      | ~ ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf('44',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('45',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','47'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['12','50'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X11 @ ( k2_pre_topc @ X11 @ X10 ) ) @ X10 )
      | ~ ( r1_tarski @ X10 @ ( k2_pre_topc @ X11 @ ( k1_tops_1 @ X11 @ X10 ) ) )
      | ( v4_tops_1 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('59',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('60',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['29','35'])).

thf('65',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['61'])).

thf('66',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('68',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['61'])).

thf('69',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['71'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ X8 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['85','90'])).

thf('92',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['69'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_tops_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ ( k2_pre_topc @ X11 @ X10 ) ) @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( X12
       != ( k1_tops_1 @ X13 @ ( k2_pre_topc @ X13 @ X12 ) ) )
      | ( v6_tops_1 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['61'])).

thf('110',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','63','66','67','68','70','72','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BzoR7Os1sU
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:36:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 174 iterations in 0.120s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.39/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.58  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.39/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.39/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(t107_tops_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( l1_pre_topc @ B ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58               ( ![D:$i]:
% 0.39/0.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.39/0.58                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.39/0.58                       ( v6_tops_1 @ D @ B ) ) & 
% 0.39/0.58                     ( ( v6_tops_1 @ C @ A ) =>
% 0.39/0.58                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( l1_pre_topc @ B ) =>
% 0.39/0.58              ( ![C:$i]:
% 0.39/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58                  ( ![D:$i]:
% 0.39/0.58                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.39/0.58                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.39/0.58                          ( v6_tops_1 @ D @ B ) ) & 
% 0.39/0.58                        ( ( v6_tops_1 @ C @ A ) =>
% 0.39/0.58                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.39/0.58  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(dt_k1_tops_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( l1_pre_topc @ A ) & 
% 0.39/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58       ( m1_subset_1 @
% 0.39/0.58         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X14 : $i, X15 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X14)
% 0.39/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.39/0.58          | (m1_subset_1 @ (k1_tops_1 @ X14 @ X15) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.58  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf(t48_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.58          | (r1_tarski @ X8 @ (k2_pre_topc @ X9 @ X8))
% 0.39/0.58          | ~ (l1_pre_topc @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.39/0.58           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.39/0.58        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(dt_k2_pre_topc, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( l1_pre_topc @ A ) & 
% 0.39/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58       ( m1_subset_1 @
% 0.39/0.58         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X6)
% 0.39/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.39/0.58          | (m1_subset_1 @ (k2_pre_topc @ X6 @ X7) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X14 : $i, X15 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X14)
% 0.39/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.39/0.58          | (m1_subset_1 @ (k1_tops_1 @ X14 @ X15) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('22', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d8_tops_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v6_tops_1 @ B @ A ) <=>
% 0.39/0.58             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X12 : $i, X13 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.58          | ~ (v6_tops_1 @ X12 @ X13)
% 0.39/0.58          | ((X12) = (k1_tops_1 @ X13 @ (k2_pre_topc @ X13 @ X12)))
% 0.39/0.58          | ~ (l1_pre_topc @ X13))),
% 0.39/0.58      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.39/0.58        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.39/0.58        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.39/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['23', '28'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf(fc9_tops_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.39/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X16)
% 0.39/0.58          | ~ (v2_pre_topc @ X16)
% 0.39/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.58          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)
% 0.39/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['29', '35'])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t56_tops_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.58                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.58          | ~ (v3_pre_topc @ X18 @ X19)
% 0.39/0.58          | ~ (r1_tarski @ X18 @ X20)
% 0.39/0.58          | (r1_tarski @ X18 @ (k1_tops_1 @ X19 @ X20))
% 0.39/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.58          | ~ (l1_pre_topc @ X19))),
% 0.39/0.58      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ sk_A)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.39/0.58          | ~ (r1_tarski @ sk_C @ X0)
% 0.39/0.58          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.58  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.39/0.58          | ~ (r1_tarski @ sk_C @ X0)
% 0.39/0.58          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (~ (r1_tarski @ sk_C @ X0)
% 0.39/0.58           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.39/0.58           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['36', '41'])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      ((((r1_tarski @ sk_C @ 
% 0.39/0.58          (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.39/0.58         | ~ (r1_tarski @ sk_C @ 
% 0.39/0.58              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))))
% 0.39/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['21', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.39/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['23', '28'])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.39/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['23', '28'])).
% 0.39/0.58  thf(d10_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.58  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.39/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['43', '44', '45', '47'])).
% 0.39/0.58  thf(t1_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.58       ( r1_tarski @ A @ C ) ))).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X3 @ X4)
% 0.39/0.58          | ~ (r1_tarski @ X4 @ X5)
% 0.39/0.58          | (r1_tarski @ X3 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.58  thf('50', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          ((r1_tarski @ sk_C @ X0)
% 0.39/0.58           | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)))
% 0.39/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.39/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '50'])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d6_tops_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58           ( ( v4_tops_1 @ B @ A ) <=>
% 0.39/0.58             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.39/0.58               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.39/0.58          | ~ (r1_tarski @ (k1_tops_1 @ X11 @ (k2_pre_topc @ X11 @ X10)) @ X10)
% 0.39/0.58          | ~ (r1_tarski @ X10 @ (k2_pre_topc @ X11 @ (k1_tops_1 @ X11 @ X10)))
% 0.39/0.58          | (v4_tops_1 @ X10 @ X11)
% 0.39/0.58          | ~ (l1_pre_topc @ X11))),
% 0.39/0.58      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | (v4_tops_1 @ sk_C @ sk_A)
% 0.39/0.58        | ~ (r1_tarski @ sk_C @ 
% 0.39/0.58             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.39/0.58        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.39/0.58             sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.39/0.58  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      (((v4_tops_1 @ sk_C @ sk_A)
% 0.39/0.58        | ~ (r1_tarski @ sk_C @ 
% 0.39/0.58             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.39/0.58        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.39/0.58             sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['54', '55'])).
% 0.39/0.58  thf('57', plain,
% 0.39/0.58      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_C)
% 0.39/0.58         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['51', '56'])).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.39/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['23', '28'])).
% 0.39/0.58  thf('59', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.39/0.58  thf('60', plain,
% 0.39/0.58      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.39/0.58        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.39/0.58        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('62', plain,
% 0.39/0.58      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['61'])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['60', '62'])).
% 0.39/0.58  thf('64', plain,
% 0.39/0.58      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['29', '35'])).
% 0.39/0.58  thf('65', plain,
% 0.39/0.58      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['61'])).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['64', '65'])).
% 0.39/0.58  thf('67', plain,
% 0.39/0.58      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['22'])).
% 0.39/0.58  thf('68', plain,
% 0.39/0.58      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.39/0.58       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['61'])).
% 0.39/0.58  thf('69', plain,
% 0.39/0.58      (((v4_tops_1 @ sk_D @ sk_B)
% 0.39/0.58        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.39/0.58        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('70', plain,
% 0.39/0.58      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.39/0.58       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['69'])).
% 0.39/0.58  thf('71', plain,
% 0.39/0.58      (((v3_pre_topc @ sk_D @ sk_B)
% 0.39/0.58        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.39/0.58        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('72', plain,
% 0.39/0.58      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.39/0.58       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['71'])).
% 0.39/0.58  thf('73', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('74', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X6)
% 0.39/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.39/0.58          | (m1_subset_1 @ (k2_pre_topc @ X6 @ X7) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.39/0.58  thf('75', plain,
% 0.39/0.58      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.39/0.58        | ~ (l1_pre_topc @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.58  thf('76', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('77', plain,
% 0.39/0.58      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('demod', [status(thm)], ['75', '76'])).
% 0.39/0.58  thf('78', plain,
% 0.39/0.58      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.39/0.58      inference('split', [status(esa)], ['71'])).
% 0.39/0.58  thf('79', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('80', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.58          | ~ (v3_pre_topc @ X18 @ X19)
% 0.39/0.58          | ~ (r1_tarski @ X18 @ X20)
% 0.39/0.58          | (r1_tarski @ X18 @ (k1_tops_1 @ X19 @ X20))
% 0.39/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.39/0.58          | ~ (l1_pre_topc @ X19))),
% 0.39/0.58      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.39/0.58  thf('81', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ sk_B)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.39/0.58          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.39/0.58          | ~ (r1_tarski @ sk_D @ X0)
% 0.39/0.58          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['79', '80'])).
% 0.39/0.58  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('83', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.39/0.58          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.39/0.58          | ~ (r1_tarski @ sk_D @ X0)
% 0.39/0.58          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['81', '82'])).
% 0.39/0.58  thf('84', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (~ (r1_tarski @ sk_D @ X0)
% 0.39/0.58           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.39/0.58           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.39/0.58         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['78', '83'])).
% 0.39/0.58  thf('85', plain,
% 0.39/0.58      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.39/0.58         | ~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.39/0.58         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['77', '84'])).
% 0.39/0.58  thf('86', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('87', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.58          | (r1_tarski @ X8 @ (k2_pre_topc @ X9 @ X8))
% 0.39/0.58          | ~ (l1_pre_topc @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.39/0.58  thf('88', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.39/0.58        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['86', '87'])).
% 0.39/0.58  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('90', plain, ((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))),
% 0.39/0.58      inference('demod', [status(thm)], ['88', '89'])).
% 0.39/0.58  thf('91', plain,
% 0.39/0.58      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.39/0.58         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.39/0.58      inference('demod', [status(thm)], ['85', '90'])).
% 0.39/0.58  thf('92', plain,
% 0.39/0.58      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.39/0.58      inference('split', [status(esa)], ['69'])).
% 0.39/0.58  thf('93', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('94', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.39/0.58          | ~ (v4_tops_1 @ X10 @ X11)
% 0.39/0.58          | (r1_tarski @ (k1_tops_1 @ X11 @ (k2_pre_topc @ X11 @ X10)) @ X10)
% 0.39/0.58          | ~ (l1_pre_topc @ X11))),
% 0.39/0.58      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.39/0.58  thf('95', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.39/0.58        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.39/0.58        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['93', '94'])).
% 0.39/0.58  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('97', plain,
% 0.39/0.58      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.39/0.58        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['95', '96'])).
% 0.39/0.58  thf('98', plain,
% 0.39/0.58      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.39/0.58         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['92', '97'])).
% 0.39/0.58  thf('99', plain,
% 0.39/0.58      (![X0 : $i, X2 : $i]:
% 0.39/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.58  thf('100', plain,
% 0.39/0.58      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.39/0.58         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.39/0.58         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['98', '99'])).
% 0.39/0.58  thf('101', plain,
% 0.39/0.58      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.39/0.58         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['91', '100'])).
% 0.39/0.58  thf('102', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('103', plain,
% 0.39/0.58      (![X12 : $i, X13 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.58          | ((X12) != (k1_tops_1 @ X13 @ (k2_pre_topc @ X13 @ X12)))
% 0.39/0.58          | (v6_tops_1 @ X12 @ X13)
% 0.39/0.58          | ~ (l1_pre_topc @ X13))),
% 0.39/0.58      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.39/0.58  thf('104', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.39/0.58        | (v6_tops_1 @ sk_D @ sk_B)
% 0.39/0.58        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['102', '103'])).
% 0.39/0.58  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('106', plain,
% 0.39/0.58      (((v6_tops_1 @ sk_D @ sk_B)
% 0.39/0.58        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.39/0.58      inference('demod', [status(thm)], ['104', '105'])).
% 0.39/0.58  thf('107', plain,
% 0.39/0.58      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.39/0.58         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['101', '106'])).
% 0.39/0.58  thf('108', plain,
% 0.39/0.58      (((v6_tops_1 @ sk_D @ sk_B))
% 0.39/0.58         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['107'])).
% 0.39/0.58  thf('109', plain,
% 0.39/0.58      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.39/0.58      inference('split', [status(esa)], ['61'])).
% 0.39/0.58  thf('110', plain,
% 0.39/0.58      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.39/0.58       ((v6_tops_1 @ sk_D @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['108', '109'])).
% 0.39/0.58  thf('111', plain, ($false),
% 0.39/0.58      inference('sat_resolution*', [status(thm)],
% 0.39/0.58                ['1', '3', '63', '66', '67', '68', '70', '72', '110'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
