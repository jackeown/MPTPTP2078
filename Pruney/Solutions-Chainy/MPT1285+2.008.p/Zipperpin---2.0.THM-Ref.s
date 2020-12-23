%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OnS3HV8Pwf

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:56 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 248 expanded)
%              Number of leaves         :   24 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          : 1049 (4369 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k1_tops_1 @ X13 @ ( k1_tops_1 @ X13 @ X14 ) )
        = ( k1_tops_1 @ X13 @ X14 ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) @ X7 )
      | ~ ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ ( k1_tops_1 @ X8 @ X7 ) ) )
      | ( v4_tops_1 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['29','34','35','37'])).

thf('39',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('45',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('54',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['56'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 )
      | ~ ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['54'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_tops_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X9
       != ( k1_tops_1 @ X10 @ ( k2_pre_topc @ X10 @ X9 ) ) )
      | ( v6_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['39'])).

thf('95',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','41','51','52','53','55','57','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OnS3HV8Pwf
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:09:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 135 iterations in 0.063s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.33/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.33/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.33/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.52  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.33/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.33/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.33/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.33/0.52  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.33/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.33/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.33/0.52  thf(t107_tops_1, conjecture,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( l1_pre_topc @ B ) =>
% 0.33/0.53           ( ![C:$i]:
% 0.33/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53               ( ![D:$i]:
% 0.33/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.33/0.53                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.33/0.53                       ( v6_tops_1 @ D @ B ) ) & 
% 0.33/0.53                     ( ( v6_tops_1 @ C @ A ) =>
% 0.33/0.53                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.53    (~( ![A:$i]:
% 0.33/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.53          ( ![B:$i]:
% 0.33/0.53            ( ( l1_pre_topc @ B ) =>
% 0.33/0.53              ( ![C:$i]:
% 0.33/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53                  ( ![D:$i]:
% 0.33/0.53                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.33/0.53                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.33/0.53                          ( v6_tops_1 @ D @ B ) ) & 
% 0.33/0.53                        ( ( v6_tops_1 @ C @ A ) =>
% 0.33/0.53                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.33/0.53    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.33/0.53  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('split', [status(esa)], ['0'])).
% 0.33/0.53  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('3', plain,
% 0.33/0.53      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('split', [status(esa)], ['2'])).
% 0.33/0.53  thf('4', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('5', plain,
% 0.33/0.53      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('split', [status(esa)], ['4'])).
% 0.33/0.53  thf('6', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(d8_tops_1, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53           ( ( v6_tops_1 @ B @ A ) <=>
% 0.33/0.53             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.33/0.53  thf('7', plain,
% 0.33/0.53      (![X9 : $i, X10 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.33/0.53          | ~ (v6_tops_1 @ X9 @ X10)
% 0.33/0.53          | ((X9) = (k1_tops_1 @ X10 @ (k2_pre_topc @ X10 @ X9)))
% 0.33/0.53          | ~ (l1_pre_topc @ X10))),
% 0.33/0.53      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.33/0.53  thf('8', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.33/0.53        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.33/0.53        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.33/0.53  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('10', plain,
% 0.33/0.53      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.33/0.53        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.33/0.53  thf('11', plain,
% 0.33/0.53      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.33/0.53         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['5', '10'])).
% 0.33/0.53  thf('12', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(dt_k2_pre_topc, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( l1_pre_topc @ A ) & 
% 0.33/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.33/0.53       ( m1_subset_1 @
% 0.33/0.53         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.33/0.53  thf('13', plain,
% 0.33/0.53      (![X3 : $i, X4 : $i]:
% 0.33/0.53         (~ (l1_pre_topc @ X3)
% 0.33/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.33/0.53          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.33/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.33/0.53      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.33/0.53  thf('14', plain,
% 0.33/0.53      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.33/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.33/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.33/0.53  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('16', plain,
% 0.33/0.53      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.33/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.33/0.53  thf(projectivity_k1_tops_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( l1_pre_topc @ A ) & 
% 0.33/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.33/0.53       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.33/0.53  thf('17', plain,
% 0.33/0.53      (![X13 : $i, X14 : $i]:
% 0.33/0.53         (~ (l1_pre_topc @ X13)
% 0.33/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.33/0.53          | ((k1_tops_1 @ X13 @ (k1_tops_1 @ X13 @ X14))
% 0.33/0.53              = (k1_tops_1 @ X13 @ X14)))),
% 0.33/0.53      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.33/0.53  thf('18', plain,
% 0.33/0.53      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.33/0.53          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.33/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.33/0.53  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('20', plain,
% 0.33/0.53      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.33/0.53         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.33/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.33/0.53  thf('21', plain,
% 0.33/0.53      ((((k1_tops_1 @ sk_A @ sk_C)
% 0.33/0.53          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.33/0.53         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['11', '20'])).
% 0.33/0.53  thf('22', plain,
% 0.33/0.53      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.33/0.53         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['5', '10'])).
% 0.33/0.53  thf('23', plain,
% 0.33/0.53      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.33/0.53  thf('24', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(d6_tops_1, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53           ( ( v4_tops_1 @ B @ A ) <=>
% 0.33/0.53             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.33/0.53               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.33/0.53  thf('25', plain,
% 0.33/0.53      (![X7 : $i, X8 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.33/0.53          | ~ (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 0.33/0.53          | ~ (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ (k1_tops_1 @ X8 @ X7)))
% 0.33/0.53          | (v4_tops_1 @ X7 @ X8)
% 0.33/0.53          | ~ (l1_pre_topc @ X8))),
% 0.33/0.53      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.33/0.53  thf('26', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.33/0.53        | (v4_tops_1 @ sk_C @ sk_A)
% 0.33/0.53        | ~ (r1_tarski @ sk_C @ 
% 0.33/0.53             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.33/0.53        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.33/0.53             sk_C))),
% 0.33/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.33/0.53  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('28', plain,
% 0.33/0.53      (((v4_tops_1 @ sk_C @ sk_A)
% 0.33/0.53        | ~ (r1_tarski @ sk_C @ 
% 0.33/0.53             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.33/0.53        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.33/0.53             sk_C))),
% 0.33/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.33/0.53  thf('29', plain,
% 0.33/0.53      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.33/0.53         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.33/0.53              sk_C)
% 0.33/0.53         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['23', '28'])).
% 0.33/0.53  thf('30', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(t48_pre_topc, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.33/0.53  thf('31', plain,
% 0.33/0.53      (![X5 : $i, X6 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.33/0.53          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ X5))
% 0.33/0.53          | ~ (l1_pre_topc @ X6))),
% 0.33/0.53      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.33/0.53  thf('32', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.33/0.53        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.33/0.53  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('34', plain, ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.33/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.33/0.53  thf('35', plain,
% 0.33/0.53      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.33/0.53         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['5', '10'])).
% 0.33/0.53  thf(d10_xboole_0, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.33/0.53  thf('36', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.33/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.33/0.53  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.33/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.33/0.53  thf('38', plain,
% 0.33/0.53      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('demod', [status(thm)], ['29', '34', '35', '37'])).
% 0.33/0.53  thf('39', plain,
% 0.33/0.53      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.33/0.53        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.33/0.53        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('40', plain,
% 0.33/0.53      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('split', [status(esa)], ['39'])).
% 0.33/0.53  thf('41', plain,
% 0.33/0.53      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['38', '40'])).
% 0.33/0.53  thf('42', plain,
% 0.33/0.53      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.33/0.53         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['5', '10'])).
% 0.33/0.53  thf('43', plain,
% 0.33/0.53      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.33/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.33/0.53  thf(fc9_tops_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.33/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.33/0.53       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.33/0.53  thf('44', plain,
% 0.33/0.53      (![X11 : $i, X12 : $i]:
% 0.33/0.53         (~ (l1_pre_topc @ X11)
% 0.33/0.53          | ~ (v2_pre_topc @ X11)
% 0.33/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.33/0.53          | (v3_pre_topc @ (k1_tops_1 @ X11 @ X12) @ X11))),
% 0.33/0.53      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.33/0.53  thf('45', plain,
% 0.33/0.53      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)
% 0.33/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.33/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.33/0.53  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('48', plain,
% 0.33/0.53      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)),
% 0.33/0.53      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.33/0.53  thf('49', plain,
% 0.33/0.53      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['42', '48'])).
% 0.33/0.53  thf('50', plain,
% 0.33/0.53      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.33/0.53      inference('split', [status(esa)], ['39'])).
% 0.33/0.53  thf('51', plain,
% 0.33/0.53      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.33/0.53  thf('52', plain,
% 0.33/0.53      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('split', [status(esa)], ['4'])).
% 0.33/0.53  thf('53', plain,
% 0.33/0.53      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.33/0.53       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('split', [status(esa)], ['39'])).
% 0.33/0.53  thf('54', plain,
% 0.33/0.53      (((v4_tops_1 @ sk_D @ sk_B)
% 0.33/0.53        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.33/0.53        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('55', plain,
% 0.33/0.53      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.33/0.53       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('split', [status(esa)], ['54'])).
% 0.33/0.53  thf('56', plain,
% 0.33/0.53      (((v3_pre_topc @ sk_D @ sk_B)
% 0.33/0.53        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.33/0.53        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('57', plain,
% 0.33/0.53      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.33/0.53       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('split', [status(esa)], ['56'])).
% 0.33/0.53  thf('58', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('59', plain,
% 0.33/0.53      (![X3 : $i, X4 : $i]:
% 0.33/0.53         (~ (l1_pre_topc @ X3)
% 0.33/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.33/0.53          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.33/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.33/0.53      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.33/0.53  thf('60', plain,
% 0.33/0.53      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.33/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.33/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.33/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.33/0.53  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('62', plain,
% 0.33/0.53      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.33/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.33/0.53  thf('63', plain,
% 0.33/0.53      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.33/0.53      inference('split', [status(esa)], ['56'])).
% 0.33/0.53  thf('64', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(t56_tops_1, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53           ( ![C:$i]:
% 0.33/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.33/0.53                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.33/0.53  thf('65', plain,
% 0.33/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.33/0.53          | ~ (v3_pre_topc @ X15 @ X16)
% 0.33/0.53          | ~ (r1_tarski @ X15 @ X17)
% 0.33/0.53          | (r1_tarski @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.33/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.33/0.53          | ~ (l1_pre_topc @ X16))),
% 0.33/0.53      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.33/0.53  thf('66', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (l1_pre_topc @ sk_B)
% 0.33/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.33/0.53          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.33/0.53          | ~ (r1_tarski @ sk_D @ X0)
% 0.33/0.53          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.33/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.33/0.53  thf('67', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('68', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.33/0.53          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.33/0.53          | ~ (r1_tarski @ sk_D @ X0)
% 0.33/0.53          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.33/0.53      inference('demod', [status(thm)], ['66', '67'])).
% 0.33/0.53  thf('69', plain,
% 0.33/0.53      ((![X0 : $i]:
% 0.33/0.53          (~ (r1_tarski @ sk_D @ X0)
% 0.33/0.53           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.33/0.53           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.33/0.53         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['63', '68'])).
% 0.33/0.53  thf('70', plain,
% 0.33/0.53      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.33/0.53         | ~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.33/0.53         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['62', '69'])).
% 0.33/0.53  thf('71', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('72', plain,
% 0.33/0.53      (![X5 : $i, X6 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.33/0.53          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ X5))
% 0.33/0.53          | ~ (l1_pre_topc @ X6))),
% 0.33/0.53      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.33/0.53  thf('73', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_B)
% 0.33/0.53        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['71', '72'])).
% 0.33/0.53  thf('74', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('75', plain, ((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))),
% 0.33/0.53      inference('demod', [status(thm)], ['73', '74'])).
% 0.33/0.53  thf('76', plain,
% 0.33/0.53      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.33/0.53         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.33/0.53      inference('demod', [status(thm)], ['70', '75'])).
% 0.33/0.53  thf('77', plain,
% 0.33/0.53      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.33/0.53      inference('split', [status(esa)], ['54'])).
% 0.33/0.53  thf('78', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('79', plain,
% 0.33/0.53      (![X7 : $i, X8 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.33/0.53          | ~ (v4_tops_1 @ X7 @ X8)
% 0.33/0.53          | (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 0.33/0.53          | ~ (l1_pre_topc @ X8))),
% 0.33/0.53      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.33/0.53  thf('80', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_B)
% 0.33/0.53        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.33/0.53        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.33/0.53      inference('sup-', [status(thm)], ['78', '79'])).
% 0.33/0.53  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('82', plain,
% 0.33/0.53      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.33/0.53        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.33/0.53      inference('demod', [status(thm)], ['80', '81'])).
% 0.33/0.53  thf('83', plain,
% 0.33/0.53      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.33/0.53         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['77', '82'])).
% 0.33/0.53  thf('84', plain,
% 0.33/0.53      (![X0 : $i, X2 : $i]:
% 0.33/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.33/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.33/0.53  thf('85', plain,
% 0.33/0.53      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.33/0.53         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.33/0.53         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['83', '84'])).
% 0.33/0.53  thf('86', plain,
% 0.33/0.53      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.33/0.53         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['76', '85'])).
% 0.33/0.53  thf('87', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('88', plain,
% 0.33/0.53      (![X9 : $i, X10 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.33/0.53          | ((X9) != (k1_tops_1 @ X10 @ (k2_pre_topc @ X10 @ X9)))
% 0.33/0.53          | (v6_tops_1 @ X9 @ X10)
% 0.33/0.53          | ~ (l1_pre_topc @ X10))),
% 0.33/0.53      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.33/0.53  thf('89', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_B)
% 0.33/0.53        | (v6_tops_1 @ sk_D @ sk_B)
% 0.33/0.53        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.33/0.53      inference('sup-', [status(thm)], ['87', '88'])).
% 0.33/0.53  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('91', plain,
% 0.33/0.53      (((v6_tops_1 @ sk_D @ sk_B)
% 0.33/0.53        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.33/0.53      inference('demod', [status(thm)], ['89', '90'])).
% 0.33/0.53  thf('92', plain,
% 0.33/0.53      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.33/0.53         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['86', '91'])).
% 0.33/0.53  thf('93', plain,
% 0.33/0.53      (((v6_tops_1 @ sk_D @ sk_B))
% 0.33/0.53         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.33/0.53      inference('simplify', [status(thm)], ['92'])).
% 0.33/0.53  thf('94', plain,
% 0.33/0.53      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.33/0.53      inference('split', [status(esa)], ['39'])).
% 0.33/0.53  thf('95', plain,
% 0.33/0.53      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.33/0.53       ((v6_tops_1 @ sk_D @ sk_B))),
% 0.33/0.53      inference('sup-', [status(thm)], ['93', '94'])).
% 0.33/0.53  thf('96', plain, ($false),
% 0.33/0.53      inference('sat_resolution*', [status(thm)],
% 0.33/0.53                ['1', '3', '41', '51', '52', '53', '55', '57', '95'])).
% 0.33/0.53  
% 0.33/0.53  % SZS output end Refutation
% 0.33/0.53  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
