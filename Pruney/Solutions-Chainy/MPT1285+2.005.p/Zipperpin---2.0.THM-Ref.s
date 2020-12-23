%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VdF2cknKth

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:55 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 517 expanded)
%              Number of leaves         :   32 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          : 1579 (9307 expanded)
%              Number of equality atoms :   31 (  88 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
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
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X19 @ ( k1_tops_1 @ X19 @ X20 ) )
        = ( k1_tops_1 @ X19 @ X20 ) ) ) ),
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

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ( v3_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) @ sk_A )
      | ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','40'])).

thf('42',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('43',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('44',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('45',plain,
    ( ( ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
      | ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('53',plain,
    ( ( v6_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('54',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X10 @ ( k2_pre_topc @ X10 @ X9 ) ) @ X9 )
      | ~ ( r1_tarski @ X9 @ ( k2_pre_topc @ X10 @ ( k1_tops_1 @ X10 @ X9 ) ) )
      | ( v4_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['60','65','66','68'])).

thf('70',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('71',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('74',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['50'])).

thf('78',plain,(
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

thf('79',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X26 )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( r1_tarski @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['84','89'])).

thf('91',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['48'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v4_tops_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_tops_1 @ X10 @ ( k2_pre_topc @ X10 @ X9 ) ) @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X13
       != ( k1_tops_1 @ X14 @ ( k2_pre_topc @ X14 @ X13 ) ) )
      | ( v6_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('109',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','1','49','51','52','53','71','109'])).

thf('111',plain,(
    ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['47','110'])).

thf('112',plain,
    ( ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['45','111'])).

thf('113',plain,
    ( ( v6_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t101_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('115',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v6_tops_1 @ X21 @ X22 )
      | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('116',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('121',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('122',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('123',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v5_tops_1 @ X11 @ X12 )
      | ( X11
        = ( k2_pre_topc @ X12 @ ( k1_tops_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) )
    | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) )
    | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['119','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('129',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('130',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('133',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X17 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('134',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['127','137'])).

thf('139',plain,(
    ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['112','138'])).

thf('140',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('141',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','139','140','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VdF2cknKth
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:23:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 991 iterations in 0.641s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.10  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.10  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.90/1.10  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.90/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.10  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.90/1.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.90/1.10  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.90/1.10  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.10  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.90/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.10  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.90/1.10  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.90/1.10  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.10  thf(t107_tops_1, conjecture,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( l1_pre_topc @ B ) =>
% 0.90/1.10           ( ![C:$i]:
% 0.90/1.10             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10               ( ![D:$i]:
% 0.90/1.10                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.90/1.10                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.90/1.10                       ( v6_tops_1 @ D @ B ) ) & 
% 0.90/1.10                     ( ( v6_tops_1 @ C @ A ) =>
% 0.90/1.10                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i]:
% 0.90/1.10        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.10          ( ![B:$i]:
% 0.90/1.10            ( ( l1_pre_topc @ B ) =>
% 0.90/1.10              ( ![C:$i]:
% 0.90/1.10                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10                  ( ![D:$i]:
% 0.90/1.10                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.90/1.10                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.90/1.10                          ( v6_tops_1 @ D @ B ) ) & 
% 0.90/1.10                        ( ( v6_tops_1 @ C @ A ) =>
% 0.90/1.10                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.90/1.10  thf('0', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('1', plain,
% 0.90/1.10      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('2', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('3', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('split', [status(esa)], ['2'])).
% 0.90/1.10  thf('4', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('5', plain,
% 0.90/1.10      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('split', [status(esa)], ['4'])).
% 0.90/1.10  thf('6', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(d8_tops_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ( v6_tops_1 @ B @ A ) <=>
% 0.90/1.10             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.10  thf('7', plain,
% 0.90/1.10      (![X13 : $i, X14 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.90/1.10          | ~ (v6_tops_1 @ X13 @ X14)
% 0.90/1.10          | ((X13) = (k1_tops_1 @ X14 @ (k2_pre_topc @ X14 @ X13)))
% 0.90/1.10          | ~ (l1_pre_topc @ X14))),
% 0.90/1.10      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.90/1.10  thf('8', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.90/1.10        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.10  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('10', plain,
% 0.90/1.10      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.90/1.10        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.10  thf('11', plain,
% 0.90/1.10      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['5', '10'])).
% 0.90/1.10  thf('12', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(dt_k2_pre_topc, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( l1_pre_topc @ A ) & 
% 0.90/1.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.10       ( m1_subset_1 @
% 0.90/1.10         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      (![X5 : $i, X6 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X5)
% 0.90/1.10          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.90/1.10          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.90/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.90/1.10  thf('14', plain,
% 0.90/1.10      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.90/1.10         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.10  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('16', plain,
% 0.90/1.10      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.10  thf(projectivity_k1_tops_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( l1_pre_topc @ A ) & 
% 0.90/1.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.10       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.90/1.10  thf('17', plain,
% 0.90/1.10      (![X19 : $i, X20 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X19)
% 0.90/1.10          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.90/1.10          | ((k1_tops_1 @ X19 @ (k1_tops_1 @ X19 @ X20))
% 0.90/1.10              = (k1_tops_1 @ X19 @ X20)))),
% 0.90/1.10      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.90/1.10  thf('18', plain,
% 0.90/1.10      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.90/1.10          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.10  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('20', plain,
% 0.90/1.10      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.90/1.10         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.90/1.10      inference('demod', [status(thm)], ['18', '19'])).
% 0.90/1.10  thf('21', plain,
% 0.90/1.10      ((((k1_tops_1 @ sk_A @ sk_C)
% 0.90/1.10          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['11', '20'])).
% 0.90/1.10  thf('22', plain,
% 0.90/1.10      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['5', '10'])).
% 0.90/1.10  thf('23', plain,
% 0.90/1.10      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['21', '22'])).
% 0.90/1.10  thf('24', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(dt_k1_tops_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( l1_pre_topc @ A ) & 
% 0.90/1.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.10       ( m1_subset_1 @
% 0.90/1.10         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.90/1.10  thf('25', plain,
% 0.90/1.10      (![X15 : $i, X16 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X15)
% 0.90/1.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.90/1.10          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 0.90/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.90/1.10  thf('26', plain,
% 0.90/1.10      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.90/1.10         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['24', '25'])).
% 0.90/1.10  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('28', plain,
% 0.90/1.10      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['26', '27'])).
% 0.90/1.10  thf('29', plain,
% 0.90/1.10      (![X5 : $i, X6 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X5)
% 0.90/1.10          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.90/1.10          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.90/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.90/1.10  thf('30', plain,
% 0.90/1.10      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.90/1.10         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.10  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('32', plain,
% 0.90/1.10      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['30', '31'])).
% 0.90/1.10  thf('33', plain,
% 0.90/1.10      (![X15 : $i, X16 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X15)
% 0.90/1.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.90/1.10          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 0.90/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.90/1.10  thf('34', plain,
% 0.90/1.10      (((m1_subset_1 @ 
% 0.90/1.10         (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.90/1.10         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['32', '33'])).
% 0.90/1.10  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('36', plain,
% 0.90/1.10      ((m1_subset_1 @ 
% 0.90/1.10        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['34', '35'])).
% 0.90/1.10  thf(t30_tops_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ( v3_pre_topc @ B @ A ) <=>
% 0.90/1.10             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.90/1.10  thf('37', plain,
% 0.90/1.10      (![X23 : $i, X24 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.90/1.10          | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.90/1.10          | (v3_pre_topc @ X23 @ X24)
% 0.90/1.10          | ~ (l1_pre_topc @ X24))),
% 0.90/1.10      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.90/1.10  thf('38', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | (v3_pre_topc @ 
% 0.90/1.10           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.90/1.10           sk_A)
% 0.90/1.10        | ~ (v4_pre_topc @ 
% 0.90/1.10             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.10              (k1_tops_1 @ sk_A @ 
% 0.90/1.10               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))) @ 
% 0.90/1.10             sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['36', '37'])).
% 0.90/1.10  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('40', plain,
% 0.90/1.10      (((v3_pre_topc @ 
% 0.90/1.10         (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.90/1.10         sk_A)
% 0.90/1.10        | ~ (v4_pre_topc @ 
% 0.90/1.10             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.10              (k1_tops_1 @ sk_A @ 
% 0.90/1.10               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))) @ 
% 0.90/1.10             sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['38', '39'])).
% 0.90/1.10  thf('41', plain,
% 0.90/1.10      (((~ (v4_pre_topc @ 
% 0.90/1.10            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.10             (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))) @ 
% 0.90/1.10            sk_A)
% 0.90/1.10         | (v3_pre_topc @ 
% 0.90/1.10            (k1_tops_1 @ sk_A @ 
% 0.90/1.10             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.90/1.10            sk_A)))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['23', '40'])).
% 0.90/1.10  thf('42', plain,
% 0.90/1.10      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['5', '10'])).
% 0.90/1.10  thf('43', plain,
% 0.90/1.10      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['21', '22'])).
% 0.90/1.10  thf('44', plain,
% 0.90/1.10      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['5', '10'])).
% 0.90/1.10  thf('45', plain,
% 0.90/1.10      (((~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.90/1.10         | (v3_pre_topc @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.90/1.10  thf('46', plain,
% 0.90/1.10      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.90/1.10        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.90/1.10        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('47', plain,
% 0.90/1.10      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.90/1.10      inference('split', [status(esa)], ['46'])).
% 0.90/1.10  thf('48', plain,
% 0.90/1.10      (((v4_tops_1 @ sk_D @ sk_B)
% 0.90/1.10        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.90/1.10        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('49', plain,
% 0.90/1.10      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.90/1.10       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('split', [status(esa)], ['48'])).
% 0.90/1.10  thf('50', plain,
% 0.90/1.10      (((v3_pre_topc @ sk_D @ sk_B)
% 0.90/1.10        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.90/1.10        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('51', plain,
% 0.90/1.10      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.90/1.10       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('split', [status(esa)], ['50'])).
% 0.90/1.10  thf('52', plain,
% 0.90/1.10      (~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_D @ sk_B)) | 
% 0.90/1.10       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('split', [status(esa)], ['46'])).
% 0.90/1.10  thf('53', plain,
% 0.90/1.10      (((v6_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_D @ sk_B))),
% 0.90/1.10      inference('split', [status(esa)], ['4'])).
% 0.90/1.10  thf('54', plain,
% 0.90/1.10      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['21', '22'])).
% 0.90/1.10  thf('55', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(d6_tops_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ( v4_tops_1 @ B @ A ) <=>
% 0.90/1.10             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.90/1.10               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf('56', plain,
% 0.90/1.10      (![X9 : $i, X10 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.90/1.10          | ~ (r1_tarski @ (k1_tops_1 @ X10 @ (k2_pre_topc @ X10 @ X9)) @ X9)
% 0.90/1.10          | ~ (r1_tarski @ X9 @ (k2_pre_topc @ X10 @ (k1_tops_1 @ X10 @ X9)))
% 0.90/1.10          | (v4_tops_1 @ X9 @ X10)
% 0.90/1.10          | ~ (l1_pre_topc @ X10))),
% 0.90/1.10      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.90/1.10  thf('57', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | (v4_tops_1 @ sk_C @ sk_A)
% 0.90/1.10        | ~ (r1_tarski @ sk_C @ 
% 0.90/1.10             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.90/1.10        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.90/1.10             sk_C))),
% 0.90/1.10      inference('sup-', [status(thm)], ['55', '56'])).
% 0.90/1.10  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('59', plain,
% 0.90/1.10      (((v4_tops_1 @ sk_C @ sk_A)
% 0.90/1.10        | ~ (r1_tarski @ sk_C @ 
% 0.90/1.10             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.90/1.10        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.90/1.10             sk_C))),
% 0.90/1.10      inference('demod', [status(thm)], ['57', '58'])).
% 0.90/1.10  thf('60', plain,
% 0.90/1.10      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.90/1.10         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.90/1.10              sk_C)
% 0.90/1.10         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['54', '59'])).
% 0.90/1.10  thf('61', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t48_pre_topc, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.90/1.10  thf('62', plain,
% 0.90/1.10      (![X7 : $i, X8 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.90/1.10          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ X7))
% 0.90/1.10          | ~ (l1_pre_topc @ X8))),
% 0.90/1.10      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.90/1.10  thf('63', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['61', '62'])).
% 0.90/1.10  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('65', plain, ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.90/1.10      inference('demod', [status(thm)], ['63', '64'])).
% 0.90/1.10  thf('66', plain,
% 0.90/1.10      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['5', '10'])).
% 0.90/1.10  thf(d10_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.10  thf('67', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.10      inference('simplify', [status(thm)], ['67'])).
% 0.90/1.10  thf('69', plain,
% 0.90/1.10      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['60', '65', '66', '68'])).
% 0.90/1.10  thf('70', plain,
% 0.90/1.10      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('split', [status(esa)], ['46'])).
% 0.90/1.10  thf('71', plain,
% 0.90/1.10      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.10  thf('72', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('73', plain,
% 0.90/1.10      (![X5 : $i, X6 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X5)
% 0.90/1.10          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.90/1.10          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.90/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.90/1.10  thf('74', plain,
% 0.90/1.10      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.90/1.10         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.90/1.10        | ~ (l1_pre_topc @ sk_B))),
% 0.90/1.10      inference('sup-', [status(thm)], ['72', '73'])).
% 0.90/1.10  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('76', plain,
% 0.90/1.10      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('demod', [status(thm)], ['74', '75'])).
% 0.90/1.10  thf('77', plain,
% 0.90/1.10      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.90/1.10      inference('split', [status(esa)], ['50'])).
% 0.90/1.10  thf('78', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t56_tops_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ![C:$i]:
% 0.90/1.10             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.90/1.10                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf('79', plain,
% 0.90/1.10      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.90/1.10          | ~ (v3_pre_topc @ X25 @ X26)
% 0.90/1.10          | ~ (r1_tarski @ X25 @ X27)
% 0.90/1.10          | (r1_tarski @ X25 @ (k1_tops_1 @ X26 @ X27))
% 0.90/1.10          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.90/1.10          | ~ (l1_pre_topc @ X26))),
% 0.90/1.10      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.90/1.10  thf('80', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ sk_B)
% 0.90/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.90/1.10          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.90/1.10          | ~ (r1_tarski @ sk_D @ X0)
% 0.90/1.10          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.90/1.10      inference('sup-', [status(thm)], ['78', '79'])).
% 0.90/1.10  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('82', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.90/1.10          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.90/1.10          | ~ (r1_tarski @ sk_D @ X0)
% 0.90/1.10          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.90/1.10      inference('demod', [status(thm)], ['80', '81'])).
% 0.90/1.10  thf('83', plain,
% 0.90/1.10      ((![X0 : $i]:
% 0.90/1.10          (~ (r1_tarski @ sk_D @ X0)
% 0.90/1.10           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.90/1.10           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.90/1.10         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['77', '82'])).
% 0.90/1.10  thf('84', plain,
% 0.90/1.10      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.90/1.10         | ~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.90/1.10         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['76', '83'])).
% 0.90/1.10  thf('85', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('86', plain,
% 0.90/1.10      (![X7 : $i, X8 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.90/1.10          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ X7))
% 0.90/1.10          | ~ (l1_pre_topc @ X8))),
% 0.90/1.10      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.90/1.10  thf('87', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_B)
% 0.90/1.10        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['85', '86'])).
% 0.90/1.10  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('89', plain, ((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))),
% 0.90/1.10      inference('demod', [status(thm)], ['87', '88'])).
% 0.90/1.10  thf('90', plain,
% 0.90/1.10      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.90/1.10         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.90/1.10      inference('demod', [status(thm)], ['84', '89'])).
% 0.90/1.10  thf('91', plain,
% 0.90/1.10      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.90/1.10      inference('split', [status(esa)], ['48'])).
% 0.90/1.10  thf('92', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('93', plain,
% 0.90/1.10      (![X9 : $i, X10 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.90/1.10          | ~ (v4_tops_1 @ X9 @ X10)
% 0.90/1.10          | (r1_tarski @ (k1_tops_1 @ X10 @ (k2_pre_topc @ X10 @ X9)) @ X9)
% 0.90/1.10          | ~ (l1_pre_topc @ X10))),
% 0.90/1.10      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.90/1.10  thf('94', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_B)
% 0.90/1.10        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.90/1.10        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.90/1.10      inference('sup-', [status(thm)], ['92', '93'])).
% 0.90/1.10  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('96', plain,
% 0.90/1.10      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.90/1.10        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.90/1.10      inference('demod', [status(thm)], ['94', '95'])).
% 0.90/1.10  thf('97', plain,
% 0.90/1.10      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.90/1.10         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['91', '96'])).
% 0.90/1.10  thf('98', plain,
% 0.90/1.10      (![X0 : $i, X2 : $i]:
% 0.90/1.10         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('99', plain,
% 0.90/1.10      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.90/1.10         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.90/1.10         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['97', '98'])).
% 0.90/1.10  thf('100', plain,
% 0.90/1.10      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.90/1.10         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['90', '99'])).
% 0.90/1.10  thf('101', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('102', plain,
% 0.90/1.10      (![X13 : $i, X14 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.90/1.10          | ((X13) != (k1_tops_1 @ X14 @ (k2_pre_topc @ X14 @ X13)))
% 0.90/1.10          | (v6_tops_1 @ X13 @ X14)
% 0.90/1.10          | ~ (l1_pre_topc @ X14))),
% 0.90/1.10      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.90/1.10  thf('103', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_B)
% 0.90/1.10        | (v6_tops_1 @ sk_D @ sk_B)
% 0.90/1.10        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['101', '102'])).
% 0.90/1.10  thf('104', plain, ((l1_pre_topc @ sk_B)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('105', plain,
% 0.90/1.10      (((v6_tops_1 @ sk_D @ sk_B)
% 0.90/1.10        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.90/1.10      inference('demod', [status(thm)], ['103', '104'])).
% 0.90/1.10  thf('106', plain,
% 0.90/1.10      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.90/1.10         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['100', '105'])).
% 0.90/1.10  thf('107', plain,
% 0.90/1.10      (((v6_tops_1 @ sk_D @ sk_B))
% 0.90/1.10         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.90/1.10      inference('simplify', [status(thm)], ['106'])).
% 0.90/1.10  thf('108', plain,
% 0.90/1.10      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.90/1.10      inference('split', [status(esa)], ['46'])).
% 0.90/1.10  thf('109', plain,
% 0.90/1.10      (((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v4_tops_1 @ sk_D @ sk_B)) | 
% 0.90/1.10       ~ ((v3_pre_topc @ sk_D @ sk_B))),
% 0.90/1.10      inference('sup-', [status(thm)], ['107', '108'])).
% 0.90/1.10  thf('110', plain, (~ ((v3_pre_topc @ sk_C @ sk_A))),
% 0.90/1.10      inference('sat_resolution*', [status(thm)],
% 0.90/1.10                ['3', '1', '49', '51', '52', '53', '71', '109'])).
% 0.90/1.10  thf('111', plain, (~ (v3_pre_topc @ sk_C @ sk_A)),
% 0.90/1.10      inference('simpl_trail', [status(thm)], ['47', '110'])).
% 0.90/1.10  thf('112', plain,
% 0.90/1.10      ((~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('clc', [status(thm)], ['45', '111'])).
% 0.90/1.10  thf('113', plain,
% 0.90/1.10      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('split', [status(esa)], ['4'])).
% 0.90/1.10  thf('114', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(t101_tops_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ( v6_tops_1 @ B @ A ) <=>
% 0.90/1.10             ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.90/1.10  thf('115', plain,
% 0.90/1.10      (![X21 : $i, X22 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.90/1.10          | ~ (v6_tops_1 @ X21 @ X22)
% 0.90/1.10          | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 0.90/1.10          | ~ (l1_pre_topc @ X22))),
% 0.90/1.10      inference('cnf', [status(esa)], [t101_tops_1])).
% 0.90/1.10  thf('116', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.90/1.10        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['114', '115'])).
% 0.90/1.10  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('118', plain,
% 0.90/1.10      (((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.90/1.10        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['116', '117'])).
% 0.90/1.10  thf('119', plain,
% 0.90/1.10      (((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['113', '118'])).
% 0.90/1.10  thf('120', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(dt_k3_subset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.10       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.90/1.10  thf('121', plain,
% 0.90/1.10      (![X3 : $i, X4 : $i]:
% 0.90/1.10         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 0.90/1.10          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.90/1.10  thf('122', plain,
% 0.90/1.10      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['120', '121'])).
% 0.90/1.10  thf(d7_tops_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( l1_pre_topc @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.10           ( ( v5_tops_1 @ B @ A ) <=>
% 0.90/1.10             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.10  thf('123', plain,
% 0.90/1.10      (![X11 : $i, X12 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.90/1.10          | ~ (v5_tops_1 @ X11 @ X12)
% 0.90/1.10          | ((X11) = (k2_pre_topc @ X12 @ (k1_tops_1 @ X12 @ X11)))
% 0.90/1.10          | ~ (l1_pre_topc @ X12))),
% 0.90/1.10      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.90/1.10  thf('124', plain,
% 0.90/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.10        | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.90/1.10            = (k2_pre_topc @ sk_A @ 
% 0.90/1.10               (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.90/1.10        | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['122', '123'])).
% 0.90/1.10  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('126', plain,
% 0.90/1.10      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.90/1.10          = (k2_pre_topc @ sk_A @ 
% 0.90/1.10             (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.90/1.10        | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['124', '125'])).
% 0.90/1.10  thf('127', plain,
% 0.90/1.10      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.90/1.10          = (k2_pre_topc @ sk_A @ 
% 0.90/1.10             (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['119', '126'])).
% 0.90/1.10  thf('128', plain,
% 0.90/1.10      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['120', '121'])).
% 0.90/1.10  thf('129', plain,
% 0.90/1.10      (![X15 : $i, X16 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X15)
% 0.90/1.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.90/1.10          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 0.90/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.90/1.10      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.90/1.10  thf('130', plain,
% 0.90/1.10      (((m1_subset_1 @ 
% 0.90/1.10         (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.90/1.10         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['128', '129'])).
% 0.90/1.10  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('132', plain,
% 0.90/1.10      ((m1_subset_1 @ 
% 0.90/1.10        (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.90/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.10      inference('demod', [status(thm)], ['130', '131'])).
% 0.90/1.10  thf(fc1_tops_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.90/1.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.10       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.90/1.10  thf('133', plain,
% 0.90/1.10      (![X17 : $i, X18 : $i]:
% 0.90/1.10         (~ (l1_pre_topc @ X17)
% 0.90/1.10          | ~ (v2_pre_topc @ X17)
% 0.90/1.10          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.90/1.10          | (v4_pre_topc @ (k2_pre_topc @ X17 @ X18) @ X17))),
% 0.90/1.10      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.90/1.10  thf('134', plain,
% 0.90/1.10      (((v4_pre_topc @ 
% 0.90/1.10         (k2_pre_topc @ sk_A @ 
% 0.90/1.10          (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))) @ 
% 0.90/1.10         sk_A)
% 0.90/1.10        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['132', '133'])).
% 0.90/1.10  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('137', plain,
% 0.90/1.10      ((v4_pre_topc @ 
% 0.90/1.10        (k2_pre_topc @ sk_A @ 
% 0.90/1.10         (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))) @ 
% 0.90/1.10        sk_A)),
% 0.90/1.10      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.90/1.10  thf('138', plain,
% 0.90/1.10      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))
% 0.90/1.10         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('sup+', [status(thm)], ['127', '137'])).
% 0.90/1.10  thf('139', plain, (~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['112', '138'])).
% 0.90/1.10  thf('140', plain,
% 0.90/1.10      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.90/1.10      inference('split', [status(esa)], ['4'])).
% 0.90/1.10  thf('141', plain, ($false),
% 0.90/1.10      inference('sat_resolution*', [status(thm)],
% 0.90/1.10                ['1', '3', '139', '140', '109'])).
% 0.90/1.10  
% 0.90/1.10  % SZS output end Refutation
% 0.90/1.10  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
