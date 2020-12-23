%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SJESgmXXVj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:56 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 358 expanded)
%              Number of leaves         :   24 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          : 1493 (6618 expanded)
%              Number of equality atoms :   44 (  87 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v6_tops_1 @ X13 @ X14 )
      | ( X13
        = ( k1_tops_1 @ X14 @ ( k2_pre_topc @ X14 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
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

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k1_tops_1 @ X15 @ ( k1_tops_1 @ X15 @ X16 ) )
        = ( k1_tops_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('18',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('23',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X12 @ ( k2_pre_topc @ X12 @ X11 ) ) @ X11 )
      | ~ ( r1_tarski @ X11 @ ( k2_pre_topc @ X12 @ ( k1_tops_1 @ X12 @ X11 ) ) )
      | ( v4_tops_1 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','32'])).

thf('34',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != X21 )
      | ( v3_pre_topc @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('48',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 )
        | ( ( k1_tops_1 @ X22 @ X21 )
         != X21 )
        | ( v3_pre_topc @ X21 @ X22 ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 )
        | ( ( k1_tops_1 @ X22 @ X21 )
         != X21 )
        | ( v3_pre_topc @ X21 @ X22 ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(split,[status(esa)],['47'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ~ ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 )
        | ( ( k1_tops_1 @ X22 @ X21 )
         != X21 )
        | ( v3_pre_topc @ X21 @ X22 ) )
    | ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(split,[status(esa)],['47'])).

thf('55',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != X21 )
      | ( v3_pre_topc @ X21 @ X22 ) ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != X21 )
      | ( v3_pre_topc @ X21 @ X22 ) ) ),
    inference(simpl_trail,[status(thm)],['48','55'])).

thf('57',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
     != sk_C )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
     != sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( ( sk_C != sk_C )
      | ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['45','60'])).

thf('62',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('64',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('66',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('67',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['67'])).

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
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['67'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X19 )
      | ( ( k1_tops_1 @ X19 @ X20 )
        = X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('74',plain,
    ( ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( v3_pre_topc @ X20 @ X19 )
        | ( ( k1_tops_1 @ X19 @ X20 )
          = X20 ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( v3_pre_topc @ X20 @ X19 )
        | ( ( k1_tops_1 @ X19 @ X20 )
          = X20 ) ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(split,[status(esa)],['73'])).

thf('77',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ~ ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( v3_pre_topc @ X20 @ X19 )
        | ( ( k1_tops_1 @ X19 @ X20 )
          = X20 ) )
    | ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(split,[status(esa)],['73'])).

thf('82',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X19 )
      | ( ( k1_tops_1 @ X19 @ X20 )
        = X20 ) ) ),
    inference('sat_resolution*',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X19 )
      | ( ( k1_tops_1 @ X19 @ X20 )
        = X20 ) ) ),
    inference(simpl_trail,[status(thm)],['74','82'])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['71','86'])).

thf('88',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['69'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_tops_1 @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k2_pre_topc @ X12 @ ( k1_tops_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['67'])).

thf('102',plain,(
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

thf('103',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ X23 @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','108'])).

thf('110',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['69'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_tops_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_tops_1 @ X12 @ ( k2_pre_topc @ X12 @ X11 ) ) @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X13
       != ( k1_tops_1 @ X14 @ ( k2_pre_topc @ X14 @ X13 ) ) )
      | ( v6_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('122',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('128',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','44','64','65','66','68','70','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SJESgmXXVj
% 0.13/0.36  % Computer   : n025.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:58:21 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.49/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.67  % Solved by: fo/fo7.sh
% 0.49/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.67  % done 368 iterations in 0.193s
% 0.49/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.67  % SZS output start Refutation
% 0.49/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.49/0.67  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.49/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.49/0.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.49/0.67  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.49/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.67  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.49/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.49/0.67  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.49/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.67  thf(t107_tops_1, conjecture,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( l1_pre_topc @ B ) =>
% 0.49/0.67           ( ![C:$i]:
% 0.49/0.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67               ( ![D:$i]:
% 0.49/0.67                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.49/0.67                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.49/0.67                       ( v6_tops_1 @ D @ B ) ) & 
% 0.49/0.67                     ( ( v6_tops_1 @ C @ A ) =>
% 0.49/0.67                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.67    (~( ![A:$i]:
% 0.49/0.67        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.67          ( ![B:$i]:
% 0.49/0.67            ( ( l1_pre_topc @ B ) =>
% 0.49/0.67              ( ![C:$i]:
% 0.49/0.67                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67                  ( ![D:$i]:
% 0.49/0.67                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.49/0.67                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.49/0.67                          ( v6_tops_1 @ D @ B ) ) & 
% 0.49/0.67                        ( ( v6_tops_1 @ C @ A ) =>
% 0.49/0.67                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.49/0.67    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.49/0.67  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('split', [status(esa)], ['0'])).
% 0.49/0.67  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('3', plain,
% 0.49/0.67      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('split', [status(esa)], ['2'])).
% 0.49/0.67  thf('4', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('5', plain,
% 0.49/0.67      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('split', [status(esa)], ['4'])).
% 0.49/0.67  thf('6', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(d8_tops_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( l1_pre_topc @ A ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67           ( ( v6_tops_1 @ B @ A ) <=>
% 0.49/0.67             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.49/0.67  thf('7', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.49/0.67          | ~ (v6_tops_1 @ X13 @ X14)
% 0.49/0.67          | ((X13) = (k1_tops_1 @ X14 @ (k2_pre_topc @ X14 @ X13)))
% 0.49/0.67          | ~ (l1_pre_topc @ X14))),
% 0.49/0.67      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.49/0.67  thf('8', plain,
% 0.49/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.67        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.49/0.67        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.49/0.67  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('10', plain,
% 0.49/0.67      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.49/0.67        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['8', '9'])).
% 0.49/0.67  thf('11', plain,
% 0.49/0.67      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.49/0.67         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['5', '10'])).
% 0.49/0.67  thf('12', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(dt_k2_pre_topc, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( l1_pre_topc @ A ) & 
% 0.49/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.67       ( m1_subset_1 @
% 0.49/0.67         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.49/0.67  thf('13', plain,
% 0.49/0.67      (![X9 : $i, X10 : $i]:
% 0.49/0.67         (~ (l1_pre_topc @ X9)
% 0.49/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.49/0.67          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 0.49/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.49/0.67  thf('14', plain,
% 0.49/0.67      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.49/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.67  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('16', plain,
% 0.49/0.67      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.49/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.49/0.67  thf(projectivity_k1_tops_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( l1_pre_topc @ A ) & 
% 0.49/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.67       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.49/0.67  thf('17', plain,
% 0.49/0.67      (![X15 : $i, X16 : $i]:
% 0.49/0.67         (~ (l1_pre_topc @ X15)
% 0.49/0.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.49/0.67          | ((k1_tops_1 @ X15 @ (k1_tops_1 @ X15 @ X16))
% 0.49/0.67              = (k1_tops_1 @ X15 @ X16)))),
% 0.49/0.67      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.49/0.67  thf('18', plain,
% 0.49/0.67      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.49/0.67          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.49/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.67  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('20', plain,
% 0.49/0.67      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.49/0.67         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.49/0.67      inference('demod', [status(thm)], ['18', '19'])).
% 0.49/0.67  thf('21', plain,
% 0.49/0.67      ((((k1_tops_1 @ sk_A @ sk_C)
% 0.49/0.67          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.49/0.67         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['11', '20'])).
% 0.49/0.67  thf('22', plain,
% 0.49/0.67      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.49/0.67         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['5', '10'])).
% 0.49/0.67  thf('23', plain,
% 0.49/0.67      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['21', '22'])).
% 0.49/0.67  thf('24', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(d6_tops_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( l1_pre_topc @ A ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67           ( ( v4_tops_1 @ B @ A ) <=>
% 0.49/0.67             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.49/0.67               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.49/0.67  thf('25', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.49/0.67          | ~ (r1_tarski @ (k1_tops_1 @ X12 @ (k2_pre_topc @ X12 @ X11)) @ X11)
% 0.49/0.67          | ~ (r1_tarski @ X11 @ (k2_pre_topc @ X12 @ (k1_tops_1 @ X12 @ X11)))
% 0.49/0.67          | (v4_tops_1 @ X11 @ X12)
% 0.49/0.67          | ~ (l1_pre_topc @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.49/0.67  thf('26', plain,
% 0.49/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.67        | (v4_tops_1 @ sk_C @ sk_A)
% 0.49/0.67        | ~ (r1_tarski @ sk_C @ 
% 0.49/0.67             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.49/0.67        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.49/0.67             sk_C))),
% 0.49/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.49/0.67  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('28', plain,
% 0.49/0.67      (((v4_tops_1 @ sk_C @ sk_A)
% 0.49/0.67        | ~ (r1_tarski @ sk_C @ 
% 0.49/0.67             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.49/0.67        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.49/0.67             sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['26', '27'])).
% 0.49/0.67  thf('29', plain,
% 0.49/0.67      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.49/0.67         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.49/0.67              sk_C)
% 0.49/0.67         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['23', '28'])).
% 0.49/0.67  thf('30', plain,
% 0.49/0.67      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.49/0.67         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['5', '10'])).
% 0.49/0.67  thf(d10_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.49/0.67  thf('31', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.49/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.49/0.67  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.49/0.67      inference('simplify', [status(thm)], ['31'])).
% 0.49/0.67  thf('33', plain,
% 0.49/0.67      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.49/0.67         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('demod', [status(thm)], ['29', '30', '32'])).
% 0.49/0.67  thf('34', plain,
% 0.49/0.67      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.49/0.67         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['5', '10'])).
% 0.49/0.67  thf('35', plain,
% 0.49/0.67      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.49/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('demod', [status(thm)], ['14', '15'])).
% 0.49/0.67  thf(t44_tops_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( l1_pre_topc @ A ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.49/0.67  thf('36', plain,
% 0.49/0.67      (![X17 : $i, X18 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.49/0.67          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ X17)
% 0.49/0.67          | ~ (l1_pre_topc @ X18))),
% 0.49/0.67      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.49/0.67  thf('37', plain,
% 0.49/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.67        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.49/0.67           (k2_pre_topc @ sk_A @ sk_C)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.67  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('39', plain,
% 0.49/0.67      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.49/0.67        (k2_pre_topc @ sk_A @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.49/0.67  thf('40', plain,
% 0.49/0.67      (((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.49/0.67         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['34', '39'])).
% 0.49/0.67  thf('41', plain,
% 0.49/0.67      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('demod', [status(thm)], ['33', '40'])).
% 0.49/0.67  thf('42', plain,
% 0.49/0.67      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.49/0.67        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.49/0.67        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('43', plain,
% 0.49/0.67      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('split', [status(esa)], ['42'])).
% 0.49/0.67  thf('44', plain,
% 0.49/0.67      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['41', '43'])).
% 0.49/0.67  thf('45', plain,
% 0.49/0.67      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['21', '22'])).
% 0.49/0.67  thf('46', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(t55_tops_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( l1_pre_topc @ B ) =>
% 0.49/0.67           ( ![C:$i]:
% 0.49/0.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67               ( ![D:$i]:
% 0.49/0.67                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.49/0.67                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.49/0.67                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.49/0.67                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.49/0.67                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.67  thf('47', plain,
% 0.49/0.67      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.67         (~ (l1_pre_topc @ X19)
% 0.49/0.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.49/0.67          | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.49/0.67          | (v3_pre_topc @ X21 @ X22)
% 0.49/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67          | ~ (l1_pre_topc @ X22)
% 0.49/0.67          | ~ (v2_pre_topc @ X22))),
% 0.49/0.67      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.49/0.67  thf('48', plain,
% 0.49/0.67      ((![X21 : $i, X22 : $i]:
% 0.49/0.67          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67           | ~ (l1_pre_topc @ X22)
% 0.49/0.67           | ~ (v2_pre_topc @ X22)
% 0.49/0.67           | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.49/0.67           | (v3_pre_topc @ X21 @ X22)))
% 0.49/0.67         <= ((![X21 : $i, X22 : $i]:
% 0.49/0.67                (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67                 | ~ (l1_pre_topc @ X22)
% 0.49/0.67                 | ~ (v2_pre_topc @ X22)
% 0.49/0.67                 | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.49/0.67                 | (v3_pre_topc @ X21 @ X22))))),
% 0.49/0.67      inference('split', [status(esa)], ['47'])).
% 0.49/0.67  thf('49', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('50', plain,
% 0.49/0.67      ((![X19 : $i, X20 : $i]:
% 0.49/0.67          (~ (l1_pre_topc @ X19)
% 0.49/0.67           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))))
% 0.49/0.67         <= ((![X19 : $i, X20 : $i]:
% 0.49/0.67                (~ (l1_pre_topc @ X19)
% 0.49/0.67                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))))),
% 0.49/0.67      inference('split', [status(esa)], ['47'])).
% 0.49/0.67  thf('51', plain,
% 0.49/0.67      ((~ (l1_pre_topc @ sk_A))
% 0.49/0.67         <= ((![X19 : $i, X20 : $i]:
% 0.49/0.67                (~ (l1_pre_topc @ X19)
% 0.49/0.67                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['49', '50'])).
% 0.49/0.67  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('53', plain,
% 0.49/0.67      (~
% 0.49/0.67       (![X19 : $i, X20 : $i]:
% 0.49/0.67          (~ (l1_pre_topc @ X19)
% 0.49/0.67           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))))),
% 0.49/0.67      inference('demod', [status(thm)], ['51', '52'])).
% 0.49/0.67  thf('54', plain,
% 0.49/0.67      ((![X21 : $i, X22 : $i]:
% 0.49/0.67          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67           | ~ (l1_pre_topc @ X22)
% 0.49/0.67           | ~ (v2_pre_topc @ X22)
% 0.49/0.67           | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.49/0.67           | (v3_pre_topc @ X21 @ X22))) | 
% 0.49/0.67       (![X19 : $i, X20 : $i]:
% 0.49/0.67          (~ (l1_pre_topc @ X19)
% 0.49/0.67           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))))),
% 0.49/0.67      inference('split', [status(esa)], ['47'])).
% 0.49/0.67  thf('55', plain,
% 0.49/0.67      ((![X21 : $i, X22 : $i]:
% 0.49/0.67          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67           | ~ (l1_pre_topc @ X22)
% 0.49/0.67           | ~ (v2_pre_topc @ X22)
% 0.49/0.67           | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.49/0.67           | (v3_pre_topc @ X21 @ X22)))),
% 0.49/0.67      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 0.49/0.67  thf('56', plain,
% 0.49/0.67      (![X21 : $i, X22 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67          | ~ (l1_pre_topc @ X22)
% 0.49/0.67          | ~ (v2_pre_topc @ X22)
% 0.49/0.67          | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.49/0.67          | (v3_pre_topc @ X21 @ X22))),
% 0.49/0.67      inference('simpl_trail', [status(thm)], ['48', '55'])).
% 0.49/0.67  thf('57', plain,
% 0.49/0.67      (((v3_pre_topc @ sk_C @ sk_A)
% 0.49/0.67        | ((k1_tops_1 @ sk_A @ sk_C) != (sk_C))
% 0.49/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['46', '56'])).
% 0.49/0.67  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('60', plain,
% 0.49/0.67      (((v3_pre_topc @ sk_C @ sk_A) | ((k1_tops_1 @ sk_A @ sk_C) != (sk_C)))),
% 0.49/0.67      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.49/0.67  thf('61', plain,
% 0.49/0.67      (((((sk_C) != (sk_C)) | (v3_pre_topc @ sk_C @ sk_A)))
% 0.49/0.67         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['45', '60'])).
% 0.49/0.67  thf('62', plain,
% 0.49/0.67      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['61'])).
% 0.49/0.67  thf('63', plain,
% 0.49/0.67      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.49/0.67      inference('split', [status(esa)], ['42'])).
% 0.49/0.67  thf('64', plain,
% 0.49/0.67      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.67  thf('65', plain,
% 0.49/0.67      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('split', [status(esa)], ['4'])).
% 0.49/0.67  thf('66', plain,
% 0.49/0.67      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.49/0.67       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('split', [status(esa)], ['42'])).
% 0.49/0.67  thf('67', plain,
% 0.49/0.67      (((v3_pre_topc @ sk_D @ sk_B)
% 0.49/0.67        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.49/0.67        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('68', plain,
% 0.49/0.67      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.49/0.67       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('split', [status(esa)], ['67'])).
% 0.49/0.67  thf('69', plain,
% 0.49/0.67      (((v4_tops_1 @ sk_D @ sk_B)
% 0.49/0.67        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.49/0.67        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('70', plain,
% 0.49/0.67      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.49/0.67       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.49/0.67      inference('split', [status(esa)], ['69'])).
% 0.49/0.67  thf('71', plain,
% 0.49/0.67      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('split', [status(esa)], ['67'])).
% 0.49/0.67  thf('72', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('73', plain,
% 0.49/0.67      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.67         (~ (l1_pre_topc @ X19)
% 0.49/0.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.49/0.67          | ~ (v3_pre_topc @ X20 @ X19)
% 0.49/0.67          | ((k1_tops_1 @ X19 @ X20) = (X20))
% 0.49/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67          | ~ (l1_pre_topc @ X22)
% 0.49/0.67          | ~ (v2_pre_topc @ X22))),
% 0.49/0.67      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.49/0.67  thf('74', plain,
% 0.49/0.67      ((![X19 : $i, X20 : $i]:
% 0.49/0.67          (~ (l1_pre_topc @ X19)
% 0.49/0.67           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.49/0.67           | ~ (v3_pre_topc @ X20 @ X19)
% 0.49/0.67           | ((k1_tops_1 @ X19 @ X20) = (X20))))
% 0.49/0.67         <= ((![X19 : $i, X20 : $i]:
% 0.49/0.67                (~ (l1_pre_topc @ X19)
% 0.49/0.67                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.49/0.67                 | ~ (v3_pre_topc @ X20 @ X19)
% 0.49/0.67                 | ((k1_tops_1 @ X19 @ X20) = (X20)))))),
% 0.49/0.67      inference('split', [status(esa)], ['73'])).
% 0.49/0.67  thf('75', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('76', plain,
% 0.49/0.67      ((![X21 : $i, X22 : $i]:
% 0.49/0.67          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67           | ~ (l1_pre_topc @ X22)
% 0.49/0.67           | ~ (v2_pre_topc @ X22)))
% 0.49/0.67         <= ((![X21 : $i, X22 : $i]:
% 0.49/0.67                (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67                 | ~ (l1_pre_topc @ X22)
% 0.49/0.67                 | ~ (v2_pre_topc @ X22))))),
% 0.49/0.67      inference('split', [status(esa)], ['73'])).
% 0.49/0.67  thf('77', plain,
% 0.49/0.67      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.49/0.67         <= ((![X21 : $i, X22 : $i]:
% 0.49/0.67                (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67                 | ~ (l1_pre_topc @ X22)
% 0.49/0.67                 | ~ (v2_pre_topc @ X22))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['75', '76'])).
% 0.49/0.67  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('80', plain,
% 0.49/0.67      (~
% 0.49/0.67       (![X21 : $i, X22 : $i]:
% 0.49/0.67          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67           | ~ (l1_pre_topc @ X22)
% 0.49/0.67           | ~ (v2_pre_topc @ X22)))),
% 0.49/0.67      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.49/0.67  thf('81', plain,
% 0.49/0.67      ((![X19 : $i, X20 : $i]:
% 0.49/0.67          (~ (l1_pre_topc @ X19)
% 0.49/0.67           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.49/0.67           | ~ (v3_pre_topc @ X20 @ X19)
% 0.49/0.67           | ((k1_tops_1 @ X19 @ X20) = (X20)))) | 
% 0.49/0.67       (![X21 : $i, X22 : $i]:
% 0.49/0.67          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.49/0.67           | ~ (l1_pre_topc @ X22)
% 0.49/0.67           | ~ (v2_pre_topc @ X22)))),
% 0.49/0.67      inference('split', [status(esa)], ['73'])).
% 0.49/0.67  thf('82', plain,
% 0.49/0.67      ((![X19 : $i, X20 : $i]:
% 0.49/0.67          (~ (l1_pre_topc @ X19)
% 0.49/0.67           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.49/0.67           | ~ (v3_pre_topc @ X20 @ X19)
% 0.49/0.67           | ((k1_tops_1 @ X19 @ X20) = (X20))))),
% 0.49/0.67      inference('sat_resolution*', [status(thm)], ['80', '81'])).
% 0.49/0.67  thf('83', plain,
% 0.49/0.67      (![X19 : $i, X20 : $i]:
% 0.49/0.67         (~ (l1_pre_topc @ X19)
% 0.49/0.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.49/0.67          | ~ (v3_pre_topc @ X20 @ X19)
% 0.49/0.67          | ((k1_tops_1 @ X19 @ X20) = (X20)))),
% 0.49/0.67      inference('simpl_trail', [status(thm)], ['74', '82'])).
% 0.49/0.67  thf('84', plain,
% 0.49/0.67      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D))
% 0.49/0.67        | ~ (v3_pre_topc @ sk_D @ sk_B)
% 0.49/0.67        | ~ (l1_pre_topc @ sk_B))),
% 0.49/0.67      inference('sup-', [status(thm)], ['72', '83'])).
% 0.49/0.67  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('86', plain,
% 0.49/0.67      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)) | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['84', '85'])).
% 0.49/0.67  thf('87', plain,
% 0.49/0.67      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.49/0.67         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['71', '86'])).
% 0.49/0.67  thf('88', plain,
% 0.49/0.67      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.49/0.67      inference('split', [status(esa)], ['69'])).
% 0.49/0.67  thf('89', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('90', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.49/0.67          | ~ (v4_tops_1 @ X11 @ X12)
% 0.49/0.67          | (r1_tarski @ X11 @ (k2_pre_topc @ X12 @ (k1_tops_1 @ X12 @ X11)))
% 0.49/0.67          | ~ (l1_pre_topc @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.49/0.67  thf('91', plain,
% 0.49/0.67      ((~ (l1_pre_topc @ sk_B)
% 0.49/0.67        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.49/0.67        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.49/0.67      inference('sup-', [status(thm)], ['89', '90'])).
% 0.49/0.67  thf('92', plain, ((l1_pre_topc @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('93', plain,
% 0.49/0.67      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.49/0.67        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.49/0.67  thf('94', plain,
% 0.49/0.67      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))
% 0.49/0.67         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['88', '93'])).
% 0.49/0.67  thf('95', plain,
% 0.49/0.67      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.49/0.67         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['87', '94'])).
% 0.49/0.67  thf('96', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('97', plain,
% 0.49/0.67      (![X9 : $i, X10 : $i]:
% 0.49/0.67         (~ (l1_pre_topc @ X9)
% 0.49/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.49/0.67          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 0.49/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.49/0.67  thf('98', plain,
% 0.49/0.67      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.49/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.49/0.67        | ~ (l1_pre_topc @ sk_B))),
% 0.49/0.67      inference('sup-', [status(thm)], ['96', '97'])).
% 0.49/0.67  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('100', plain,
% 0.49/0.67      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.49/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.49/0.67      inference('demod', [status(thm)], ['98', '99'])).
% 0.49/0.67  thf('101', plain,
% 0.49/0.67      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('split', [status(esa)], ['67'])).
% 0.49/0.67  thf('102', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(t56_tops_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( l1_pre_topc @ A ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67           ( ![C:$i]:
% 0.49/0.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.67               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.49/0.67                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.49/0.67  thf('103', plain,
% 0.49/0.67      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.49/0.67          | ~ (v3_pre_topc @ X23 @ X24)
% 0.49/0.67          | ~ (r1_tarski @ X23 @ X25)
% 0.49/0.67          | (r1_tarski @ X23 @ (k1_tops_1 @ X24 @ X25))
% 0.49/0.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.49/0.67          | ~ (l1_pre_topc @ X24))),
% 0.49/0.67      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.49/0.67  thf('104', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (~ (l1_pre_topc @ sk_B)
% 0.49/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.49/0.67          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.49/0.67          | ~ (r1_tarski @ sk_D @ X0)
% 0.49/0.67          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.49/0.67      inference('sup-', [status(thm)], ['102', '103'])).
% 0.49/0.67  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('106', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.49/0.67          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.49/0.67          | ~ (r1_tarski @ sk_D @ X0)
% 0.49/0.67          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['104', '105'])).
% 0.49/0.67  thf('107', plain,
% 0.49/0.67      ((![X0 : $i]:
% 0.49/0.67          (~ (r1_tarski @ sk_D @ X0)
% 0.49/0.67           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.49/0.67           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.49/0.67         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['101', '106'])).
% 0.49/0.67  thf('108', plain,
% 0.49/0.67      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.49/0.67         | ~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.49/0.67         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['100', '107'])).
% 0.49/0.67  thf('109', plain,
% 0.49/0.67      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.49/0.67         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['95', '108'])).
% 0.49/0.67  thf('110', plain,
% 0.49/0.67      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.49/0.67      inference('split', [status(esa)], ['69'])).
% 0.49/0.67  thf('111', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('112', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.49/0.67          | ~ (v4_tops_1 @ X11 @ X12)
% 0.49/0.67          | (r1_tarski @ (k1_tops_1 @ X12 @ (k2_pre_topc @ X12 @ X11)) @ X11)
% 0.49/0.67          | ~ (l1_pre_topc @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.49/0.67  thf('113', plain,
% 0.49/0.67      ((~ (l1_pre_topc @ sk_B)
% 0.49/0.67        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.49/0.67        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.49/0.67      inference('sup-', [status(thm)], ['111', '112'])).
% 0.49/0.67  thf('114', plain, ((l1_pre_topc @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('115', plain,
% 0.49/0.67      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.49/0.67        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['113', '114'])).
% 0.49/0.67  thf('116', plain,
% 0.49/0.67      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.49/0.67         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['110', '115'])).
% 0.49/0.67  thf('117', plain,
% 0.49/0.67      (![X0 : $i, X2 : $i]:
% 0.49/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.49/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.49/0.67  thf('118', plain,
% 0.49/0.67      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.49/0.67         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.49/0.67         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['116', '117'])).
% 0.49/0.67  thf('119', plain,
% 0.49/0.67      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.49/0.67         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['109', '118'])).
% 0.49/0.67  thf('120', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('121', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.49/0.67          | ((X13) != (k1_tops_1 @ X14 @ (k2_pre_topc @ X14 @ X13)))
% 0.49/0.67          | (v6_tops_1 @ X13 @ X14)
% 0.49/0.67          | ~ (l1_pre_topc @ X14))),
% 0.49/0.67      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.49/0.67  thf('122', plain,
% 0.49/0.67      ((~ (l1_pre_topc @ sk_B)
% 0.49/0.67        | (v6_tops_1 @ sk_D @ sk_B)
% 0.49/0.67        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['120', '121'])).
% 0.49/0.67  thf('123', plain, ((l1_pre_topc @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('124', plain,
% 0.49/0.67      (((v6_tops_1 @ sk_D @ sk_B)
% 0.49/0.67        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.49/0.67      inference('demod', [status(thm)], ['122', '123'])).
% 0.49/0.67  thf('125', plain,
% 0.49/0.67      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.49/0.67         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['119', '124'])).
% 0.49/0.67  thf('126', plain,
% 0.49/0.67      (((v6_tops_1 @ sk_D @ sk_B))
% 0.49/0.67         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['125'])).
% 0.49/0.67  thf('127', plain,
% 0.49/0.67      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.49/0.67      inference('split', [status(esa)], ['42'])).
% 0.49/0.67  thf('128', plain,
% 0.49/0.67      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.49/0.67       ((v6_tops_1 @ sk_D @ sk_B))),
% 0.49/0.67      inference('sup-', [status(thm)], ['126', '127'])).
% 0.49/0.67  thf('129', plain, ($false),
% 0.49/0.67      inference('sat_resolution*', [status(thm)],
% 0.49/0.67                ['1', '3', '44', '64', '65', '66', '68', '70', '128'])).
% 0.49/0.67  
% 0.49/0.67  % SZS output end Refutation
% 0.49/0.67  
% 0.49/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
