%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c7VpQUzgNM

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:56 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 334 expanded)
%              Number of leaves         :   23 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          : 1285 (5886 expanded)
%              Number of equality atoms :   22 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v6_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v6_tops_1 @ X7 @ X8 )
      | ( X7
        = ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
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

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('19',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['12','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ sk_C @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['4','29'])).

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
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X12 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X6 @ ( k2_pre_topc @ X6 @ X5 ) ) @ X5 )
      | ~ ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ ( k1_tops_1 @ X6 @ X5 ) ) )
      | ( v4_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X12 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('56',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('57',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['47','54','55','56'])).

thf('58',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['12','22'])).

thf('62',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('63',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('65',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('66',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['68'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ sk_D ) )
      | ~ ( r1_tarski @ sk_D @ sk_D ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('80',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ sk_D ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X12 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ sk_D ) )
    | ( sk_D
      = ( k1_tops_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ sk_D ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_tops_1 @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ ( k1_tops_1 @ X6 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['88','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('103',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','103'])).

thf('105',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_tops_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_tops_1 @ X6 @ ( k2_pre_topc @ X6 @ X5 ) ) @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('113',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X7
       != ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) )
      | ( v6_tops_1 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('117',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['58'])).

thf('123',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','60','63','64','65','67','69','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c7VpQUzgNM
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 134 iterations in 0.112s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.58  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.37/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.58  thf(t107_tops_1, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( l1_pre_topc @ B ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58               ( ![D:$i]:
% 0.37/0.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.58                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.37/0.58                       ( v6_tops_1 @ D @ B ) ) & 
% 0.37/0.58                     ( ( v6_tops_1 @ C @ A ) =>
% 0.37/0.58                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( l1_pre_topc @ B ) =>
% 0.37/0.58              ( ![C:$i]:
% 0.37/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58                  ( ![D:$i]:
% 0.37/0.58                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.58                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.37/0.58                          ( v6_tops_1 @ D @ B ) ) & 
% 0.37/0.58                        ( ( v6_tops_1 @ C @ A ) =>
% 0.37/0.58                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.37/0.58  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.58      inference('split', [status(esa)], ['0'])).
% 0.37/0.58  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.58      inference('split', [status(esa)], ['2'])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('5', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['5'])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(d8_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( v6_tops_1 @ B @ A ) <=>
% 0.37/0.58             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X7 : $i, X8 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.37/0.58          | ~ (v6_tops_1 @ X7 @ X8)
% 0.37/0.58          | ((X7) = (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)))
% 0.37/0.58          | ~ (l1_pre_topc @ X8))),
% 0.37/0.58      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.37/0.58        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.58  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.37/0.58        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.37/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(dt_k2_pre_topc, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58       ( m1_subset_1 @
% 0.37/0.58         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ X3)
% 0.37/0.58          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.37/0.58          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.37/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.37/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.58  thf(fc9_tops_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.37/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X9 : $i, X10 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ X9)
% 0.37/0.58          | ~ (v2_pre_topc @ X9)
% 0.37/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.37/0.58          | (v3_pre_topc @ (k1_tops_1 @ X9 @ X10) @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.58  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)),
% 0.37/0.58      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['12', '22'])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t56_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.58                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.58          | ~ (v3_pre_topc @ X13 @ X14)
% 0.37/0.58          | ~ (r1_tarski @ X13 @ X15)
% 0.37/0.58          | (r1_tarski @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.37/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.58          | ~ (l1_pre_topc @ X14))),
% 0.37/0.58      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ sk_A)
% 0.37/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.37/0.58          | ~ (r1_tarski @ sk_C @ X0)
% 0.37/0.58          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.58  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.37/0.58          | ~ (r1_tarski @ sk_C @ X0)
% 0.37/0.58          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      ((![X0 : $i]:
% 0.37/0.58          (~ (r1_tarski @ sk_C @ X0)
% 0.37/0.58           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.37/0.58           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['23', '28'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C))
% 0.37/0.58         | ~ (r1_tarski @ sk_C @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['4', '29'])).
% 0.37/0.58  thf(d10_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.58  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['30', '32'])).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t44_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.58          | (r1_tarski @ (k1_tops_1 @ X12 @ X11) @ X11)
% 0.37/0.58          | ~ (l1_pre_topc @ X12))),
% 0.37/0.58      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.58  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('38', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.37/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (![X0 : $i, X2 : $i]:
% 0.37/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      ((~ (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C))
% 0.37/0.58        | ((sk_C) = (k1_tops_1 @ sk_A @ sk_C)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.58  thf('41', plain,
% 0.37/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '40'])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(d6_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( v4_tops_1 @ B @ A ) <=>
% 0.37/0.58             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.37/0.58               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf('43', plain,
% 0.37/0.58      (![X5 : $i, X6 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.58          | ~ (r1_tarski @ (k1_tops_1 @ X6 @ (k2_pre_topc @ X6 @ X5)) @ X5)
% 0.37/0.58          | ~ (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ (k1_tops_1 @ X6 @ X5)))
% 0.37/0.58          | (v4_tops_1 @ X5 @ X6)
% 0.37/0.58          | ~ (l1_pre_topc @ X6))),
% 0.37/0.58      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v4_tops_1 @ sk_C @ sk_A)
% 0.37/0.58        | ~ (r1_tarski @ sk_C @ 
% 0.37/0.58             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.58        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.58             sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.58  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (((v4_tops_1 @ sk_C @ sk_A)
% 0.37/0.58        | ~ (r1_tarski @ sk_C @ 
% 0.37/0.58             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.37/0.58        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.58             sk_C))),
% 0.37/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.37/0.58         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.58              sk_C)
% 0.37/0.58         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['41', '46'])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.37/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      (![X11 : $i, X12 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.58          | (r1_tarski @ (k1_tops_1 @ X12 @ X11) @ X11)
% 0.37/0.58          | ~ (l1_pre_topc @ X12))),
% 0.37/0.58      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.58           (k2_pre_topc @ sk_A @ sk_C)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.58  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.37/0.58        (k2_pre_topc @ sk_A @ sk_C))),
% 0.37/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      (((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.37/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['48', '53'])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.37/0.58         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.37/0.58  thf('56', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.59      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.59  thf('57', plain,
% 0.37/0.59      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['47', '54', '55', '56'])).
% 0.37/0.59  thf('58', plain,
% 0.37/0.59      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.37/0.59        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.37/0.59        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('59', plain,
% 0.37/0.59      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.59      inference('split', [status(esa)], ['58'])).
% 0.37/0.59  thf('60', plain,
% 0.37/0.59      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['57', '59'])).
% 0.37/0.59  thf('61', plain,
% 0.37/0.59      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['12', '22'])).
% 0.37/0.59  thf('62', plain,
% 0.37/0.59      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.37/0.59      inference('split', [status(esa)], ['58'])).
% 0.37/0.59  thf('63', plain,
% 0.37/0.59      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.59  thf('64', plain,
% 0.37/0.59      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.37/0.59      inference('split', [status(esa)], ['5'])).
% 0.37/0.59  thf('65', plain,
% 0.37/0.59      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.37/0.59       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.59      inference('split', [status(esa)], ['58'])).
% 0.37/0.59  thf('66', plain,
% 0.37/0.59      (((v4_tops_1 @ sk_D @ sk_B)
% 0.37/0.59        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.37/0.59        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('67', plain,
% 0.37/0.59      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.37/0.59       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.59      inference('split', [status(esa)], ['66'])).
% 0.37/0.59  thf('68', plain,
% 0.37/0.59      (((v3_pre_topc @ sk_D @ sk_B)
% 0.37/0.59        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.37/0.59        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('69', plain,
% 0.37/0.59      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.37/0.59       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.37/0.59      inference('split', [status(esa)], ['68'])).
% 0.37/0.59  thf('70', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('71', plain,
% 0.37/0.59      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['68'])).
% 0.37/0.59  thf('72', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('73', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.59          | ~ (v3_pre_topc @ X13 @ X14)
% 0.37/0.59          | ~ (r1_tarski @ X13 @ X15)
% 0.37/0.59          | (r1_tarski @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.37/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.59          | ~ (l1_pre_topc @ X14))),
% 0.37/0.59      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.37/0.59  thf('74', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (l1_pre_topc @ sk_B)
% 0.37/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.59          | ~ (r1_tarski @ sk_D @ X0)
% 0.37/0.59          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['72', '73'])).
% 0.37/0.59  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('76', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.59          | ~ (r1_tarski @ sk_D @ X0)
% 0.37/0.59          | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['74', '75'])).
% 0.37/0.59  thf('77', plain,
% 0.37/0.59      ((![X0 : $i]:
% 0.37/0.59          (~ (r1_tarski @ sk_D @ X0)
% 0.37/0.59           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.59           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.37/0.59         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['71', '76'])).
% 0.37/0.59  thf('78', plain,
% 0.37/0.59      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ sk_D))
% 0.37/0.59         | ~ (r1_tarski @ sk_D @ sk_D))) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['70', '77'])).
% 0.37/0.59  thf('79', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.59      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.59  thf('80', plain,
% 0.37/0.59      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.37/0.59         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['78', '79'])).
% 0.37/0.59  thf('81', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('82', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.59          | (r1_tarski @ (k1_tops_1 @ X12 @ X11) @ X11)
% 0.37/0.59          | ~ (l1_pre_topc @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.37/0.59  thf('83', plain,
% 0.37/0.59      ((~ (l1_pre_topc @ sk_B) | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['81', '82'])).
% 0.37/0.59  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('85', plain, ((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ sk_D)),
% 0.37/0.59      inference('demod', [status(thm)], ['83', '84'])).
% 0.37/0.59  thf('86', plain,
% 0.37/0.59      (![X0 : $i, X2 : $i]:
% 0.37/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.59  thf('87', plain,
% 0.37/0.59      ((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ sk_D))
% 0.37/0.59        | ((sk_D) = (k1_tops_1 @ sk_B @ sk_D)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['85', '86'])).
% 0.37/0.59  thf('88', plain,
% 0.37/0.59      ((((sk_D) = (k1_tops_1 @ sk_B @ sk_D)))
% 0.37/0.59         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['80', '87'])).
% 0.37/0.59  thf('89', plain,
% 0.37/0.59      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['66'])).
% 0.37/0.59  thf('90', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('91', plain,
% 0.37/0.59      (![X5 : $i, X6 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.59          | ~ (v4_tops_1 @ X5 @ X6)
% 0.37/0.59          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ (k1_tops_1 @ X6 @ X5)))
% 0.37/0.59          | ~ (l1_pre_topc @ X6))),
% 0.37/0.59      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.37/0.59  thf('92', plain,
% 0.37/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.59        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.37/0.59        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['90', '91'])).
% 0.37/0.59  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('94', plain,
% 0.37/0.59      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.37/0.59        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['92', '93'])).
% 0.37/0.59  thf('95', plain,
% 0.37/0.59      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))
% 0.37/0.59         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['89', '94'])).
% 0.37/0.59  thf('96', plain,
% 0.37/0.59      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.37/0.59         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['88', '95'])).
% 0.37/0.59  thf('97', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('98', plain,
% 0.37/0.59      (![X3 : $i, X4 : $i]:
% 0.37/0.59         (~ (l1_pre_topc @ X3)
% 0.37/0.59          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.37/0.59          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.37/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.37/0.59      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.59  thf('99', plain,
% 0.37/0.59      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.37/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.37/0.59        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.37/0.59  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('101', plain,
% 0.37/0.59      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.37/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['99', '100'])).
% 0.37/0.59  thf('102', plain,
% 0.37/0.59      ((![X0 : $i]:
% 0.37/0.59          (~ (r1_tarski @ sk_D @ X0)
% 0.37/0.59           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ X0))
% 0.37/0.59           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.37/0.59         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['71', '76'])).
% 0.37/0.59  thf('103', plain,
% 0.37/0.59      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.37/0.59         | ~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.37/0.59         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['101', '102'])).
% 0.37/0.59  thf('104', plain,
% 0.37/0.59      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.37/0.59         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['96', '103'])).
% 0.37/0.59  thf('105', plain,
% 0.37/0.59      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['66'])).
% 0.37/0.59  thf('106', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('107', plain,
% 0.37/0.59      (![X5 : $i, X6 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.37/0.59          | ~ (v4_tops_1 @ X5 @ X6)
% 0.37/0.59          | (r1_tarski @ (k1_tops_1 @ X6 @ (k2_pre_topc @ X6 @ X5)) @ X5)
% 0.37/0.59          | ~ (l1_pre_topc @ X6))),
% 0.37/0.59      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.37/0.59  thf('108', plain,
% 0.37/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.59        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.37/0.59        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['106', '107'])).
% 0.37/0.59  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('110', plain,
% 0.37/0.59      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.37/0.59        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.37/0.59      inference('demod', [status(thm)], ['108', '109'])).
% 0.37/0.59  thf('111', plain,
% 0.37/0.59      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.37/0.59         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['105', '110'])).
% 0.37/0.59  thf('112', plain,
% 0.37/0.59      (![X0 : $i, X2 : $i]:
% 0.37/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.59  thf('113', plain,
% 0.37/0.59      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.37/0.59         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.37/0.59         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['111', '112'])).
% 0.37/0.59  thf('114', plain,
% 0.37/0.59      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.37/0.59         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['104', '113'])).
% 0.37/0.59  thf('115', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('116', plain,
% 0.37/0.59      (![X7 : $i, X8 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.37/0.59          | ((X7) != (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)))
% 0.37/0.59          | (v6_tops_1 @ X7 @ X8)
% 0.37/0.59          | ~ (l1_pre_topc @ X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.37/0.59  thf('117', plain,
% 0.37/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.59        | (v6_tops_1 @ sk_D @ sk_B)
% 0.37/0.59        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['115', '116'])).
% 0.37/0.59  thf('118', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('119', plain,
% 0.37/0.59      (((v6_tops_1 @ sk_D @ sk_B)
% 0.37/0.59        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.37/0.59      inference('demod', [status(thm)], ['117', '118'])).
% 0.37/0.59  thf('120', plain,
% 0.37/0.59      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.37/0.59         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['114', '119'])).
% 0.37/0.59  thf('121', plain,
% 0.37/0.59      (((v6_tops_1 @ sk_D @ sk_B))
% 0.37/0.59         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['120'])).
% 0.37/0.59  thf('122', plain,
% 0.37/0.59      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['58'])).
% 0.37/0.59  thf('123', plain,
% 0.37/0.59      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.37/0.59       ((v6_tops_1 @ sk_D @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['121', '122'])).
% 0.37/0.59  thf('124', plain, ($false),
% 0.37/0.59      inference('sat_resolution*', [status(thm)],
% 0.37/0.59                ['1', '3', '60', '63', '64', '65', '67', '69', '123'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
