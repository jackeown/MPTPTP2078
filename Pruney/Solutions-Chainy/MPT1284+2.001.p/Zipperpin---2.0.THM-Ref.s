%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IBtG73ZFAj

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:53 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 339 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          : 1299 (6017 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t106_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( v4_pre_topc @ D @ B )
                        & ( v4_tops_1 @ D @ B ) )
                     => ( v5_tops_1 @ D @ B ) )
                    & ( ( v5_tops_1 @ C @ A )
                     => ( ( v4_pre_topc @ C @ A )
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
                   => ( ( ( ( v4_pre_topc @ D @ B )
                          & ( v4_tops_1 @ D @ B ) )
                       => ( v5_tops_1 @ D @ B ) )
                      & ( ( v5_tops_1 @ C @ A )
                       => ( ( v4_pre_topc @ C @ A )
                          & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_tops_1])).

thf('0',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v5_tops_1 @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v5_tops_1 @ X14 @ X15 )
      | ( X14
        = ( k2_pre_topc @ X15 @ ( k1_tops_1 @ X15 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X13 @ ( k2_pre_topc @ X13 @ X12 ) ) @ X12 )
      | ~ ( r1_tarski @ X12 @ ( k2_pre_topc @ X13 @ ( k1_tops_1 @ X13 @ X12 ) ) )
      | ( v4_tops_1 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ~ ( r1_tarski @ sk_C @ sk_C )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_pre_topc @ X5 @ ( k2_pre_topc @ X5 @ X6 ) )
        = ( k2_pre_topc @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('28',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('33',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ sk_C ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','33','40'])).

thf('42',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( sk_C
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('46',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('52',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
   <= ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['45','56'])).

thf('58',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
   <= ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('59',plain,
    ( ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('61',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('62',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v4_pre_topc @ sk_D @ sk_B )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['64'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('69',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( r1_tarski @ ( k2_pre_topc @ X21 @ X22 ) @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ~ ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D )
      | ~ ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_D )
        | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ sk_D ) @ sk_D )
      | ~ ( r1_tarski @ sk_D @ sk_D ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('76',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ sk_D ) @ sk_D )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ X7 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ sk_D ) @ sk_D )
    | ( ( k2_pre_topc @ sk_B @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_pre_topc @ sk_B @ sk_D )
      = sk_D )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['62'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_tops_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ ( k2_pre_topc @ X13 @ X12 ) ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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

thf('92',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['84','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_D )
        | ( r1_tarski @ ( k2_pre_topc @ sk_B @ X0 ) @ sk_D )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('99',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ) )
   <= ( v4_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['62'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_tops_1 @ X12 @ X13 )
      | ( r1_tarski @ X12 @ ( k2_pre_topc @ X13 @ ( k1_tops_1 @ X13 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('109',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) @ sk_D )
      | ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
        = sk_D ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) )
      = sk_D )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( X14
       != ( k2_pre_topc @ X15 @ ( k1_tops_1 @ X15 @ X14 ) ) )
      | ( v5_tops_1 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( sk_D != sk_D )
      | ( v5_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,
    ( ( v5_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v4_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ~ ( v5_tops_1 @ sk_D @ sk_B )
   <= ~ ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('119',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v4_pre_topc @ sk_D @ sk_B )
    | ( v5_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','44','59','60','61','63','65','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IBtG73ZFAj
% 0.17/0.37  % Computer   : n017.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 16:03:02 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 230 iterations in 0.130s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.62  thf(t106_tops_1, conjecture,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( l1_pre_topc @ B ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62               ( ![D:$i]:
% 0.37/0.62                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.62                   ( ( ( ( v4_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.37/0.62                       ( v5_tops_1 @ D @ B ) ) & 
% 0.37/0.62                     ( ( v5_tops_1 @ C @ A ) =>
% 0.37/0.62                       ( ( v4_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i]:
% 0.37/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.62          ( ![B:$i]:
% 0.37/0.62            ( ( l1_pre_topc @ B ) =>
% 0.37/0.62              ( ![C:$i]:
% 0.37/0.62                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62                  ( ![D:$i]:
% 0.37/0.62                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.62                      ( ( ( ( v4_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.37/0.62                          ( v5_tops_1 @ D @ B ) ) & 
% 0.37/0.62                        ( ( v5_tops_1 @ C @ A ) =>
% 0.37/0.62                          ( ( v4_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t106_tops_1])).
% 0.37/0.62  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('2', plain, (((v4_pre_topc @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (((v4_pre_topc @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['2'])).
% 0.37/0.62  thf('4', plain, ((~ (v5_tops_1 @ sk_D @ sk_B) | (v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (((v5_tops_1 @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['4'])).
% 0.37/0.62  thf('6', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(d7_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( v5_tops_1 @ B @ A ) <=>
% 0.37/0.62             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf('7', plain,
% 0.37/0.62      (![X14 : $i, X15 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.62          | ~ (v5_tops_1 @ X14 @ X15)
% 0.37/0.62          | ((X14) = (k2_pre_topc @ X15 @ (k1_tops_1 @ X15 @ X14)))
% 0.37/0.62          | ~ (l1_pre_topc @ X15))),
% 0.37/0.62      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | ((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62        | ~ (v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.62  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62        | ~ (v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.62  thf('11', plain,
% 0.37/0.62      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.37/0.62         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.62  thf('12', plain,
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
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.62          | ~ (r1_tarski @ (k1_tops_1 @ X13 @ (k2_pre_topc @ X13 @ X12)) @ X12)
% 0.37/0.62          | ~ (r1_tarski @ X12 @ (k2_pre_topc @ X13 @ (k1_tops_1 @ X13 @ X12)))
% 0.37/0.62          | (v4_tops_1 @ X12 @ X13)
% 0.37/0.62          | ~ (l1_pre_topc @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | (v4_tops_1 @ sk_C @ sk_A)
% 0.37/0.62        | ~ (r1_tarski @ sk_C @ 
% 0.37/0.62             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.62             sk_C))),
% 0.37/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.62  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_C @ sk_A)
% 0.37/0.62        | ~ (r1_tarski @ sk_C @ 
% 0.37/0.62             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.62             sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      (((~ (r1_tarski @ sk_C @ sk_C)
% 0.37/0.62         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.62              sk_C)
% 0.37/0.62         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['11', '16'])).
% 0.37/0.62  thf(d10_xboole_0, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.62  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_C)
% 0.37/0.62         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['17', '19'])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.37/0.62         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(dt_k1_tops_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62       ( m1_subset_1 @
% 0.37/0.62         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (![X16 : $i, X17 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X16)
% 0.37/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.62          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.37/0.62  thf('24', plain,
% 0.37/0.62      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.37/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.62  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('26', plain,
% 0.37/0.62      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.62  thf(projectivity_k2_pre_topc, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.37/0.62         ( k2_pre_topc @ A @ B ) ) ))).
% 0.37/0.62  thf('27', plain,
% 0.37/0.62      (![X5 : $i, X6 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X5)
% 0.37/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.37/0.62          | ((k2_pre_topc @ X5 @ (k2_pre_topc @ X5 @ X6))
% 0.37/0.62              = (k2_pre_topc @ X5 @ X6)))),
% 0.37/0.62      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.62  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.37/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      ((((k2_pre_topc @ sk_A @ sk_C)
% 0.37/0.62          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.37/0.62         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['21', '30'])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.37/0.62         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      ((((sk_C) = (k2_pre_topc @ sk_A @ sk_C)))
% 0.37/0.62         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.37/0.62         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.62  thf(t48_pre_topc, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.37/0.62  thf('36', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.37/0.62          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ X7))
% 0.37/0.62          | ~ (l1_pre_topc @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.37/0.62  thf('37', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.62        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.37/0.62           (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('39', plain,
% 0.37/0.62      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.37/0.62        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.37/0.62      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.62  thf('40', plain,
% 0.37/0.62      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 0.37/0.62         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['34', '39'])).
% 0.37/0.62  thf('41', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '33', '40'])).
% 0.37/0.62  thf('42', plain,
% 0.37/0.62      ((~ (v5_tops_1 @ sk_D @ sk_B)
% 0.37/0.62        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('43', plain,
% 0.37/0.62      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['42'])).
% 0.37/0.62  thf('44', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['41', '43'])).
% 0.37/0.62  thf('45', plain,
% 0.37/0.62      ((((sk_C) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.37/0.62         <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.62  thf('46', plain,
% 0.37/0.62      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.62  thf(dt_k2_pre_topc, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62       ( m1_subset_1 @
% 0.37/0.62         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.62  thf('47', plain,
% 0.37/0.62      (![X3 : $i, X4 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X3)
% 0.37/0.62          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.37/0.62          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.62  thf('48', plain,
% 0.37/0.62      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.37/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.62  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('50', plain,
% 0.37/0.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.37/0.62  thf(fc1_tops_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.37/0.62  thf('51', plain,
% 0.37/0.62      (![X18 : $i, X19 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X18)
% 0.37/0.62          | ~ (v2_pre_topc @ X18)
% 0.37/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.62          | (v4_pre_topc @ (k2_pre_topc @ X18 @ X19) @ X18))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.37/0.62  thf('52', plain,
% 0.37/0.62      (((v4_pre_topc @ 
% 0.37/0.62         (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))) @ 
% 0.37/0.62         sk_A)
% 0.37/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.62  thf('53', plain,
% 0.37/0.62      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.62         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.37/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('56', plain,
% 0.37/0.62      ((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_A)),
% 0.37/0.62      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.37/0.62  thf('57', plain,
% 0.37/0.62      (((v4_pre_topc @ sk_C @ sk_A)) <= (((v5_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['45', '56'])).
% 0.37/0.62  thf('58', plain,
% 0.37/0.62      ((~ (v4_pre_topc @ sk_C @ sk_A)) <= (~ ((v4_pre_topc @ sk_C @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['42'])).
% 0.37/0.62  thf('59', plain,
% 0.37/0.62      (((v4_pre_topc @ sk_C @ sk_A)) | ~ ((v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.62  thf('60', plain,
% 0.37/0.62      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ((v5_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['4'])).
% 0.37/0.62  thf('61', plain,
% 0.37/0.62      (~ ((v5_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.37/0.62       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['42'])).
% 0.37/0.62  thf('62', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_D @ sk_B)
% 0.37/0.62        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('63', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.37/0.62       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['62'])).
% 0.37/0.62  thf('64', plain,
% 0.37/0.62      (((v4_pre_topc @ sk_D @ sk_B)
% 0.37/0.62        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('65', plain,
% 0.37/0.62      (((v4_pre_topc @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_C @ sk_A)) | 
% 0.37/0.62       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('split', [status(esa)], ['64'])).
% 0.37/0.62  thf('66', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('67', plain,
% 0.37/0.62      (((v4_pre_topc @ sk_D @ sk_B)) <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['64'])).
% 0.37/0.62  thf('68', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t31_tops_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_pre_topc @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ![C:$i]:
% 0.37/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.37/0.62                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf('69', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.62          | ~ (v4_pre_topc @ X20 @ X21)
% 0.37/0.62          | ~ (r1_tarski @ X22 @ X20)
% 0.37/0.62          | (r1_tarski @ (k2_pre_topc @ X21 @ X22) @ X20)
% 0.37/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.62          | ~ (l1_pre_topc @ X21))),
% 0.37/0.62      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.37/0.62  thf('70', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.37/0.62          | ~ (r1_tarski @ X0 @ sk_D)
% 0.37/0.62          | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.62  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('72', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62          | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.37/0.62          | ~ (r1_tarski @ X0 @ sk_D)
% 0.37/0.62          | ~ (v4_pre_topc @ sk_D @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.62  thf('73', plain,
% 0.37/0.62      ((![X0 : $i]:
% 0.37/0.62          (~ (r1_tarski @ X0 @ sk_D)
% 0.37/0.62           | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.37/0.62           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.37/0.62         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['67', '72'])).
% 0.37/0.62  thf('74', plain,
% 0.37/0.62      ((((r1_tarski @ (k2_pre_topc @ sk_B @ sk_D) @ sk_D)
% 0.37/0.62         | ~ (r1_tarski @ sk_D @ sk_D))) <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['66', '73'])).
% 0.37/0.62  thf('75', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.62  thf('76', plain,
% 0.37/0.62      (((r1_tarski @ (k2_pre_topc @ sk_B @ sk_D) @ sk_D))
% 0.37/0.62         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['74', '75'])).
% 0.37/0.62  thf('77', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('78', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.37/0.62          | (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ X7))
% 0.37/0.62          | ~ (l1_pre_topc @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.37/0.62  thf('79', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.37/0.62  thf('80', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('81', plain, ((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['79', '80'])).
% 0.37/0.62  thf('82', plain,
% 0.37/0.62      (![X0 : $i, X2 : $i]:
% 0.37/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.62  thf('83', plain,
% 0.37/0.62      ((~ (r1_tarski @ (k2_pre_topc @ sk_B @ sk_D) @ sk_D)
% 0.37/0.62        | ((k2_pre_topc @ sk_B @ sk_D) = (sk_D)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['81', '82'])).
% 0.37/0.62  thf('84', plain,
% 0.37/0.62      ((((k2_pre_topc @ sk_B @ sk_D) = (sk_D)))
% 0.37/0.62         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['76', '83'])).
% 0.37/0.62  thf('85', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['62'])).
% 0.37/0.62  thf('86', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('87', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.62          | ~ (v4_tops_1 @ X12 @ X13)
% 0.37/0.62          | (r1_tarski @ (k1_tops_1 @ X13 @ (k2_pre_topc @ X13 @ X12)) @ X12)
% 0.37/0.62          | ~ (l1_pre_topc @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.37/0.62  thf('88', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['86', '87'])).
% 0.37/0.62  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('90', plain,
% 0.37/0.62      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.37/0.62        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['88', '89'])).
% 0.37/0.62  thf('91', plain,
% 0.37/0.62      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['85', '90'])).
% 0.37/0.62  thf('92', plain,
% 0.37/0.62      (((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['84', '91'])).
% 0.37/0.62  thf('93', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('94', plain,
% 0.37/0.62      (![X16 : $i, X17 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ X16)
% 0.37/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.62          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.37/0.62  thf('95', plain,
% 0.37/0.62      (((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.37/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['93', '94'])).
% 0.37/0.62  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('97', plain,
% 0.37/0.62      ((m1_subset_1 @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['95', '96'])).
% 0.37/0.62  thf('98', plain,
% 0.37/0.62      ((![X0 : $i]:
% 0.37/0.62          (~ (r1_tarski @ X0 @ sk_D)
% 0.37/0.62           | (r1_tarski @ (k2_pre_topc @ sk_B @ X0) @ sk_D)
% 0.37/0.62           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.37/0.62         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['67', '72'])).
% 0.37/0.62  thf('99', plain,
% 0.37/0.62      ((((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D)
% 0.37/0.62         | ~ (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D)))
% 0.37/0.62         <= (((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['97', '98'])).
% 0.37/0.62  thf('100', plain,
% 0.37/0.62      (((r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['92', '99'])).
% 0.37/0.62  thf('101', plain,
% 0.37/0.62      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['62'])).
% 0.37/0.62  thf('102', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('103', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.62          | ~ (v4_tops_1 @ X12 @ X13)
% 0.37/0.62          | (r1_tarski @ X12 @ (k2_pre_topc @ X13 @ (k1_tops_1 @ X13 @ X12)))
% 0.37/0.62          | ~ (l1_pre_topc @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.37/0.62  thf('104', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.37/0.62        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['102', '103'])).
% 0.37/0.62  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('106', plain,
% 0.37/0.62      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.37/0.62        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('demod', [status(thm)], ['104', '105'])).
% 0.37/0.62  thf('107', plain,
% 0.37/0.62      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['101', '106'])).
% 0.37/0.62  thf('108', plain,
% 0.37/0.62      (![X0 : $i, X2 : $i]:
% 0.37/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.62  thf('109', plain,
% 0.37/0.62      (((~ (r1_tarski @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) @ sk_D)
% 0.37/0.62         | ((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D))))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['107', '108'])).
% 0.37/0.62  thf('110', plain,
% 0.37/0.62      ((((k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)) = (sk_D)))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['100', '109'])).
% 0.37/0.62  thf('111', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('112', plain,
% 0.37/0.62      (![X14 : $i, X15 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.62          | ((X14) != (k2_pre_topc @ X15 @ (k1_tops_1 @ X15 @ X14)))
% 0.37/0.62          | (v5_tops_1 @ X14 @ X15)
% 0.37/0.62          | ~ (l1_pre_topc @ X15))),
% 0.37/0.62      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.37/0.62  thf('113', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.62        | (v5_tops_1 @ sk_D @ sk_B)
% 0.37/0.62        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['111', '112'])).
% 0.37/0.62  thf('114', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('115', plain,
% 0.37/0.62      (((v5_tops_1 @ sk_D @ sk_B)
% 0.37/0.62        | ((sk_D) != (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))),
% 0.37/0.62      inference('demod', [status(thm)], ['113', '114'])).
% 0.37/0.62  thf('116', plain,
% 0.37/0.62      (((((sk_D) != (sk_D)) | (v5_tops_1 @ sk_D @ sk_B)))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['110', '115'])).
% 0.37/0.62  thf('117', plain,
% 0.37/0.62      (((v5_tops_1 @ sk_D @ sk_B))
% 0.37/0.62         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v4_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['116'])).
% 0.37/0.62  thf('118', plain,
% 0.37/0.62      ((~ (v5_tops_1 @ sk_D @ sk_B)) <= (~ ((v5_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['42'])).
% 0.37/0.62  thf('119', plain,
% 0.37/0.62      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v4_pre_topc @ sk_D @ sk_B)) | 
% 0.37/0.62       ((v5_tops_1 @ sk_D @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['117', '118'])).
% 0.37/0.62  thf('120', plain, ($false),
% 0.37/0.62      inference('sat_resolution*', [status(thm)],
% 0.37/0.62                ['1', '3', '44', '59', '60', '61', '63', '65', '119'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
