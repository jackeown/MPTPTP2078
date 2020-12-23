%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AgVKyhBM83

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:19 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  156 (1689 expanded)
%              Number of leaves         :   34 ( 491 expanded)
%              Depth                    :   28
%              Number of atoms          : 1220 (31916 expanded)
%              Number of equality atoms :   29 ( 130 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(t84_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( r2_xboole_0 @ C @ D )
                  <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m2_orders_2 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m2_orders_2 @ D @ A @ B )
                   => ( ( r2_xboole_0 @ C @ D )
                    <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_orders_2])).

thf('0',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_1 )
   <= ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,(
    m2_orders_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m2_orders_2 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf(t67_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_orders_2 @ C @ A @ B )
             => ( r1_tarski @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_orders_2 @ X17 @ X16 @ X15 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_D_1 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_C @ sk_D_1 )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('29',plain,
    ( ( ( sk_C = sk_D_1 )
      | ( r2_xboole_0 @ sk_C @ sk_D_1 ) )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
   <= ~ ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( sk_C = sk_D_1 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
   <= ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t69_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( B != k1_xboole_0 )
                  & ( m1_orders_2 @ B @ A @ C )
                  & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X18 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X20 @ X19 @ X18 )
      | ~ ( m1_orders_2 @ X18 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_orders_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('51',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(d16_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v6_orders_2 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( m2_orders_2 @ C @ A @ B )
              <=> ( ( C != k1_xboole_0 )
                  & ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ C )
                       => ( ( k1_funct_1 @ B @ ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) )
                          = D ) ) ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_orders_1 @ X5 @ ( k1_orders_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m2_orders_2 @ X7 @ X6 @ X5 )
      | ( X7 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v6_orders_2 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v3_orders_2 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X6 @ X5 )
      | ~ ( m1_orders_1 @ X5 @ ( k1_orders_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('56',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v6_orders_2 @ X14 @ X12 )
      | ~ ( m2_orders_2 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    v6_orders_2 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['56','66'])).

thf('68',plain,
    ( ( v6_orders_2 @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['55','67'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['54','68','69','70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','75'])).

thf('77',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('78',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( r2_xboole_0 @ sk_C @ sk_D_1 )
      & ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_1 )
    | ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,
    ( ( r2_xboole_0 @ sk_C @ sk_D_1 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,(
    r2_xboole_0 @ sk_C @ sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['3','80','81'])).

thf('83',plain,(
    r2_xboole_0 @ sk_C @ sk_D_1 ),
    inference(simpl_trail,[status(thm)],['1','82'])).

thf('84',plain,(
    m2_orders_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m2_orders_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( C != D )
                   => ( ( m1_orders_2 @ C @ A @ D )
                    <=> ~ ( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_orders_1 @ X21 @ ( k1_orders_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m2_orders_2 @ X23 @ X22 @ X21 )
      | ( m1_orders_2 @ X23 @ X22 @ X24 )
      | ( m1_orders_2 @ X24 @ X22 @ X23 )
      | ( X24 = X23 )
      | ~ ( m2_orders_2 @ X24 @ X22 @ X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( m1_orders_2 @ sk_C @ sk_A @ X0 )
      | ( sk_C = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_1 )
    | ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ( m1_orders_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['84','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('97',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_orders_2 @ X17 @ X16 @ X15 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
    | ( sk_C = sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','105'])).

thf('107',plain,
    ( ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 )
   <= ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('108',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','80'])).

thf('109',plain,(
    ~ ( m1_orders_2 @ sk_C @ sk_A @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C = sk_D_1 ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( sk_C = sk_D_1 )
    | ( r1_tarski @ sk_D_1 @ sk_C ) ),
    inference(clc,[status(thm)],['110','111'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('113',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('114',plain,
    ( ( sk_C = sk_D_1 )
    | ~ ( r2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    r2_xboole_0 @ sk_C @ sk_D_1 ),
    inference(simpl_trail,[status(thm)],['1','82'])).

thf('116',plain,(
    sk_C = sk_D_1 ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    r2_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['83','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('119',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    $false ),
    inference('sup-',[status(thm)],['117','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AgVKyhBM83
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:20:18 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.18/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.50  % Solved by: fo/fo7.sh
% 0.18/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.50  % done 124 iterations in 0.055s
% 0.18/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.50  % SZS output start Refutation
% 0.18/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.50  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.18/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.50  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.18/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.18/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.18/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.18/0.50  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.18/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.50  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.18/0.50  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.18/0.50  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.18/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.18/0.50  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.18/0.50  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.18/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.50  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.18/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.18/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.18/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.18/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.50  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.18/0.50  thf(t84_orders_2, conjecture,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.18/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.18/0.50       ( ![B:$i]:
% 0.18/0.50         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.50           ( ![C:$i]:
% 0.18/0.50             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.18/0.50               ( ![D:$i]:
% 0.18/0.50                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.18/0.50                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 0.18/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.50    (~( ![A:$i]:
% 0.18/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.18/0.50            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.18/0.50          ( ![B:$i]:
% 0.18/0.50            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.50              ( ![C:$i]:
% 0.18/0.50                ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.18/0.50                  ( ![D:$i]:
% 0.18/0.50                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.18/0.50                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 0.18/0.50    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 0.18/0.50  thf('0', plain,
% 0.18/0.50      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1) | (r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('1', plain,
% 0.18/0.50      (((r2_xboole_0 @ sk_C @ sk_D_1)) <= (((r2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.18/0.50      inference('split', [status(esa)], ['0'])).
% 0.18/0.50  thf('2', plain,
% 0.18/0.50      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D_1)
% 0.18/0.50        | ~ (r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('3', plain,
% 0.18/0.50      (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)) | 
% 0.18/0.50       ~ ((r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.18/0.50      inference('split', [status(esa)], ['2'])).
% 0.18/0.50  thf('4', plain,
% 0.18/0.50      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('5', plain,
% 0.18/0.50      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))
% 0.18/0.50         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('split', [status(esa)], ['0'])).
% 0.18/0.50  thf('6', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('7', plain,
% 0.18/0.50      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf(dt_m2_orders_2, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.18/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.18/0.50         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.50       ( ![C:$i]:
% 0.18/0.50         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.18/0.50           ( ( v6_orders_2 @ C @ A ) & 
% 0.18/0.50             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.18/0.50  thf('8', plain,
% 0.18/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.18/0.50         (~ (l1_orders_2 @ X12)
% 0.18/0.50          | ~ (v5_orders_2 @ X12)
% 0.18/0.50          | ~ (v4_orders_2 @ X12)
% 0.18/0.50          | ~ (v3_orders_2 @ X12)
% 0.18/0.50          | (v2_struct_0 @ X12)
% 0.18/0.50          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X12)))
% 0.18/0.50          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.18/0.50          | ~ (m2_orders_2 @ X14 @ X12 @ X13))),
% 0.18/0.50      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.18/0.50  thf('9', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.18/0.50          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.50          | (v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.18/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.18/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.50  thf('10', plain, ((v3_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('11', plain, ((v4_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('12', plain, ((v5_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('14', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.18/0.50          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.50          | (v2_struct_0 @ sk_A))),
% 0.18/0.50      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.18/0.50  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('16', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.18/0.50      inference('clc', [status(thm)], ['14', '15'])).
% 0.18/0.50  thf('17', plain,
% 0.18/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['6', '16'])).
% 0.18/0.50  thf(t67_orders_2, axiom,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.18/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.18/0.50       ( ![B:$i]:
% 0.18/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.50           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 0.18/0.50  thf('18', plain,
% 0.18/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.18/0.50         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.18/0.50          | (r1_tarski @ X17 @ X15)
% 0.18/0.50          | ~ (m1_orders_2 @ X17 @ X16 @ X15)
% 0.18/0.50          | ~ (l1_orders_2 @ X16)
% 0.18/0.50          | ~ (v5_orders_2 @ X16)
% 0.18/0.50          | ~ (v4_orders_2 @ X16)
% 0.18/0.50          | ~ (v3_orders_2 @ X16)
% 0.18/0.50          | (v2_struct_0 @ X16))),
% 0.18/0.50      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.18/0.50  thf('19', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.18/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.18/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.18/0.50          | (r1_tarski @ X0 @ sk_D_1))),
% 0.18/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.18/0.50  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('24', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 0.18/0.50          | (r1_tarski @ X0 @ sk_D_1))),
% 0.18/0.50      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.18/0.50  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('26', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((r1_tarski @ X0 @ sk_D_1) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1))),
% 0.18/0.50      inference('clc', [status(thm)], ['24', '25'])).
% 0.18/0.50  thf('27', plain,
% 0.18/0.50      (((r1_tarski @ sk_C @ sk_D_1))
% 0.18/0.50         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['5', '26'])).
% 0.18/0.50  thf(d8_xboole_0, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.18/0.50       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.18/0.50  thf('28', plain,
% 0.18/0.50      (![X0 : $i, X2 : $i]:
% 0.18/0.50         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.18/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.18/0.50  thf('29', plain,
% 0.18/0.50      (((((sk_C) = (sk_D_1)) | (r2_xboole_0 @ sk_C @ sk_D_1)))
% 0.18/0.50         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.18/0.50  thf('30', plain,
% 0.18/0.50      ((~ (r2_xboole_0 @ sk_C @ sk_D_1)) <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.18/0.50      inference('split', [status(esa)], ['2'])).
% 0.18/0.50  thf('31', plain,
% 0.18/0.50      ((((sk_C) = (sk_D_1)))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.18/0.50  thf('32', plain,
% 0.18/0.50      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))
% 0.18/0.50         <= (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('split', [status(esa)], ['0'])).
% 0.18/0.50  thf('33', plain,
% 0.18/0.50      (((m1_orders_2 @ sk_C @ sk_A @ sk_C))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup+', [status(thm)], ['31', '32'])).
% 0.18/0.50  thf('34', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('35', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.18/0.50      inference('clc', [status(thm)], ['14', '15'])).
% 0.18/0.50  thf('36', plain,
% 0.18/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.50  thf('37', plain,
% 0.18/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.50  thf(t69_orders_2, axiom,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.18/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.18/0.50       ( ![B:$i]:
% 0.18/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.50           ( ![C:$i]:
% 0.18/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.50               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.18/0.50                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 0.18/0.50  thf('38', plain,
% 0.18/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.18/0.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.18/0.50          | ((X18) = (k1_xboole_0))
% 0.18/0.50          | ~ (m1_orders_2 @ X20 @ X19 @ X18)
% 0.18/0.50          | ~ (m1_orders_2 @ X18 @ X19 @ X20)
% 0.18/0.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.18/0.50          | ~ (l1_orders_2 @ X19)
% 0.18/0.50          | ~ (v5_orders_2 @ X19)
% 0.18/0.50          | ~ (v4_orders_2 @ X19)
% 0.18/0.50          | ~ (v3_orders_2 @ X19)
% 0.18/0.50          | (v2_struct_0 @ X19))),
% 0.18/0.50      inference('cnf', [status(esa)], [t69_orders_2])).
% 0.18/0.50  thf('39', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.18/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.18/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.50          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.18/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.18/0.50          | ((sk_C) = (k1_xboole_0)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.18/0.50  thf('40', plain, ((v3_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('41', plain, ((v4_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('42', plain, ((v5_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('44', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.50          | ~ (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.18/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.18/0.50          | ((sk_C) = (k1_xboole_0)))),
% 0.18/0.50      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.18/0.50  thf('45', plain,
% 0.18/0.50      ((((sk_C) = (k1_xboole_0))
% 0.18/0.50        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.18/0.50        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.18/0.50        | (v2_struct_0 @ sk_A))),
% 0.18/0.50      inference('sup-', [status(thm)], ['36', '44'])).
% 0.18/0.50  thf('46', plain,
% 0.18/0.50      (((v2_struct_0 @ sk_A)
% 0.18/0.50        | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C)
% 0.18/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.18/0.50      inference('simplify', [status(thm)], ['45'])).
% 0.18/0.50  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('48', plain,
% 0.18/0.50      ((((sk_C) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C @ sk_A @ sk_C))),
% 0.18/0.50      inference('clc', [status(thm)], ['46', '47'])).
% 0.18/0.50  thf('49', plain,
% 0.18/0.50      ((((sk_C) = (k1_xboole_0)))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['33', '48'])).
% 0.18/0.50  thf('50', plain,
% 0.18/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.50  thf('51', plain,
% 0.18/0.50      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup+', [status(thm)], ['49', '50'])).
% 0.18/0.50  thf(d16_orders_2, axiom,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.18/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.18/0.50       ( ![B:$i]:
% 0.18/0.50         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.50           ( ![C:$i]:
% 0.18/0.50             ( ( ( v6_orders_2 @ C @ A ) & 
% 0.18/0.50                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.18/0.50               ( ( m2_orders_2 @ C @ A @ B ) <=>
% 0.18/0.50                 ( ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.18/0.50                   ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C ) & 
% 0.18/0.50                   ( ![D:$i]:
% 0.18/0.50                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.18/0.50                       ( ( r2_hidden @ D @ C ) =>
% 0.18/0.50                         ( ( k1_funct_1 @
% 0.18/0.50                             B @ 
% 0.18/0.50                             ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) ) =
% 0.18/0.50                           ( D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.50  thf('52', plain,
% 0.18/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.18/0.50         (~ (m1_orders_1 @ X5 @ (k1_orders_1 @ (u1_struct_0 @ X6)))
% 0.18/0.50          | ~ (m2_orders_2 @ X7 @ X6 @ X5)
% 0.18/0.50          | ((X7) != (k1_xboole_0))
% 0.18/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.18/0.50          | ~ (v6_orders_2 @ X7 @ X6)
% 0.18/0.50          | ~ (l1_orders_2 @ X6)
% 0.18/0.50          | ~ (v5_orders_2 @ X6)
% 0.18/0.50          | ~ (v4_orders_2 @ X6)
% 0.18/0.50          | ~ (v3_orders_2 @ X6)
% 0.18/0.50          | (v2_struct_0 @ X6))),
% 0.18/0.50      inference('cnf', [status(esa)], [d16_orders_2])).
% 0.18/0.50  thf('53', plain,
% 0.18/0.50      (![X5 : $i, X6 : $i]:
% 0.18/0.50         ((v2_struct_0 @ X6)
% 0.18/0.50          | ~ (v3_orders_2 @ X6)
% 0.18/0.50          | ~ (v4_orders_2 @ X6)
% 0.18/0.50          | ~ (v5_orders_2 @ X6)
% 0.18/0.50          | ~ (l1_orders_2 @ X6)
% 0.18/0.50          | ~ (v6_orders_2 @ k1_xboole_0 @ X6)
% 0.18/0.50          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.18/0.50          | ~ (m2_orders_2 @ k1_xboole_0 @ X6 @ X5)
% 0.18/0.50          | ~ (m1_orders_1 @ X5 @ (k1_orders_1 @ (u1_struct_0 @ X6))))),
% 0.18/0.50      inference('simplify', [status(thm)], ['52'])).
% 0.18/0.50  thf('54', plain,
% 0.18/0.50      ((![X0 : $i]:
% 0.18/0.50          (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.50           | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.18/0.50           | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.18/0.50           | ~ (l1_orders_2 @ sk_A)
% 0.18/0.50           | ~ (v5_orders_2 @ sk_A)
% 0.18/0.50           | ~ (v4_orders_2 @ sk_A)
% 0.18/0.50           | ~ (v3_orders_2 @ sk_A)
% 0.18/0.50           | (v2_struct_0 @ sk_A)))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['51', '53'])).
% 0.18/0.50  thf('55', plain,
% 0.18/0.50      ((((sk_C) = (k1_xboole_0)))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['33', '48'])).
% 0.18/0.50  thf('56', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('57', plain,
% 0.18/0.50      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('58', plain,
% 0.18/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.18/0.50         (~ (l1_orders_2 @ X12)
% 0.18/0.50          | ~ (v5_orders_2 @ X12)
% 0.18/0.50          | ~ (v4_orders_2 @ X12)
% 0.18/0.50          | ~ (v3_orders_2 @ X12)
% 0.18/0.50          | (v2_struct_0 @ X12)
% 0.18/0.50          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X12)))
% 0.18/0.50          | (v6_orders_2 @ X14 @ X12)
% 0.18/0.50          | ~ (m2_orders_2 @ X14 @ X12 @ X13))),
% 0.18/0.50      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.18/0.50  thf('59', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.18/0.50          | (v6_orders_2 @ X0 @ sk_A)
% 0.18/0.50          | (v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.18/0.50          | ~ (l1_orders_2 @ sk_A))),
% 0.18/0.50      inference('sup-', [status(thm)], ['57', '58'])).
% 0.18/0.50  thf('60', plain, ((v3_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('61', plain, ((v4_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('62', plain, ((v5_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('63', plain, ((l1_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('64', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.18/0.50          | (v6_orders_2 @ X0 @ sk_A)
% 0.18/0.50          | (v2_struct_0 @ sk_A))),
% 0.18/0.50      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 0.18/0.50  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('66', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.18/0.50      inference('clc', [status(thm)], ['64', '65'])).
% 0.18/0.50  thf('67', plain, ((v6_orders_2 @ sk_C @ sk_A)),
% 0.18/0.50      inference('sup-', [status(thm)], ['56', '66'])).
% 0.18/0.50  thf('68', plain,
% 0.18/0.50      (((v6_orders_2 @ k1_xboole_0 @ sk_A))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup+', [status(thm)], ['55', '67'])).
% 0.18/0.50  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('70', plain, ((v5_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('71', plain, ((v4_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('72', plain, ((v3_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('73', plain,
% 0.18/0.50      ((![X0 : $i]:
% 0.18/0.50          (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.18/0.50           | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.18/0.50           | (v2_struct_0 @ sk_A)))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('demod', [status(thm)], ['54', '68', '69', '70', '71', '72'])).
% 0.18/0.50  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('75', plain,
% 0.18/0.50      ((![X0 : $i]:
% 0.18/0.50          (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.18/0.50           | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('clc', [status(thm)], ['73', '74'])).
% 0.18/0.50  thf('76', plain,
% 0.18/0.50      ((~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['4', '75'])).
% 0.18/0.50  thf('77', plain,
% 0.18/0.50      ((((sk_C) = (k1_xboole_0)))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['33', '48'])).
% 0.18/0.50  thf('78', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('79', plain,
% 0.18/0.50      (((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.18/0.50         <= (~ ((r2_xboole_0 @ sk_C @ sk_D_1)) & 
% 0.18/0.50             ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('sup+', [status(thm)], ['77', '78'])).
% 0.18/0.50  thf('80', plain,
% 0.18/0.50      (((r2_xboole_0 @ sk_C @ sk_D_1)) | 
% 0.18/0.50       ~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))),
% 0.18/0.50      inference('demod', [status(thm)], ['76', '79'])).
% 0.18/0.50  thf('81', plain,
% 0.18/0.50      (((r2_xboole_0 @ sk_C @ sk_D_1)) | ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))),
% 0.18/0.50      inference('split', [status(esa)], ['0'])).
% 0.18/0.50  thf('82', plain, (((r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.18/0.50      inference('sat_resolution*', [status(thm)], ['3', '80', '81'])).
% 0.18/0.50  thf('83', plain, ((r2_xboole_0 @ sk_C @ sk_D_1)),
% 0.18/0.50      inference('simpl_trail', [status(thm)], ['1', '82'])).
% 0.18/0.50  thf('84', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('85', plain, ((m2_orders_2 @ sk_C @ sk_A @ sk_B)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('86', plain,
% 0.18/0.50      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf(t83_orders_2, axiom,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.18/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.18/0.50       ( ![B:$i]:
% 0.18/0.50         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.18/0.50           ( ![C:$i]:
% 0.18/0.50             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.18/0.50               ( ![D:$i]:
% 0.18/0.50                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 0.18/0.50                   ( ( ( C ) != ( D ) ) =>
% 0.18/0.50                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 0.18/0.50                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.50  thf('87', plain,
% 0.18/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.18/0.50         (~ (m1_orders_1 @ X21 @ (k1_orders_1 @ (u1_struct_0 @ X22)))
% 0.18/0.50          | ~ (m2_orders_2 @ X23 @ X22 @ X21)
% 0.18/0.50          | (m1_orders_2 @ X23 @ X22 @ X24)
% 0.18/0.50          | (m1_orders_2 @ X24 @ X22 @ X23)
% 0.18/0.50          | ((X24) = (X23))
% 0.18/0.50          | ~ (m2_orders_2 @ X24 @ X22 @ X21)
% 0.18/0.50          | ~ (l1_orders_2 @ X22)
% 0.18/0.50          | ~ (v5_orders_2 @ X22)
% 0.18/0.50          | ~ (v4_orders_2 @ X22)
% 0.18/0.50          | ~ (v3_orders_2 @ X22)
% 0.18/0.50          | (v2_struct_0 @ X22))),
% 0.18/0.50      inference('cnf', [status(esa)], [t83_orders_2])).
% 0.18/0.50  thf('88', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]:
% 0.18/0.50         ((v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.18/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.18/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.18/0.50          | ((X0) = (X1))
% 0.18/0.50          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.18/0.50          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.18/0.50          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.18/0.50      inference('sup-', [status(thm)], ['86', '87'])).
% 0.18/0.50  thf('89', plain, ((v3_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('90', plain, ((v4_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('91', plain, ((v5_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('93', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]:
% 0.18/0.50         ((v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.18/0.50          | ((X0) = (X1))
% 0.18/0.50          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 0.18/0.50          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 0.18/0.50          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.18/0.50      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.18/0.50  thf('94', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.18/0.50          | (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.18/0.50          | (m1_orders_2 @ sk_C @ sk_A @ X0)
% 0.18/0.50          | ((sk_C) = (X0))
% 0.18/0.50          | (v2_struct_0 @ sk_A))),
% 0.18/0.50      inference('sup-', [status(thm)], ['85', '93'])).
% 0.18/0.50  thf('95', plain,
% 0.18/0.50      (((v2_struct_0 @ sk_A)
% 0.18/0.50        | ((sk_C) = (sk_D_1))
% 0.18/0.50        | (m1_orders_2 @ sk_C @ sk_A @ sk_D_1)
% 0.18/0.50        | (m1_orders_2 @ sk_D_1 @ sk_A @ sk_C))),
% 0.18/0.50      inference('sup-', [status(thm)], ['84', '94'])).
% 0.18/0.50  thf('96', plain,
% 0.18/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.50  thf('97', plain,
% 0.18/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.18/0.50         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.18/0.50          | (r1_tarski @ X17 @ X15)
% 0.18/0.50          | ~ (m1_orders_2 @ X17 @ X16 @ X15)
% 0.18/0.50          | ~ (l1_orders_2 @ X16)
% 0.18/0.50          | ~ (v5_orders_2 @ X16)
% 0.18/0.50          | ~ (v4_orders_2 @ X16)
% 0.18/0.50          | ~ (v3_orders_2 @ X16)
% 0.18/0.50          | (v2_struct_0 @ X16))),
% 0.18/0.50      inference('cnf', [status(esa)], [t67_orders_2])).
% 0.18/0.50  thf('98', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.18/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.18/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.18/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.18/0.50          | (r1_tarski @ X0 @ sk_C))),
% 0.18/0.50      inference('sup-', [status(thm)], ['96', '97'])).
% 0.18/0.50  thf('99', plain, ((v3_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('100', plain, ((v4_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('101', plain, ((v5_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('102', plain, ((l1_orders_2 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('103', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((v2_struct_0 @ sk_A)
% 0.18/0.50          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C)
% 0.18/0.50          | (r1_tarski @ X0 @ sk_C))),
% 0.18/0.50      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.18/0.50  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('105', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((r1_tarski @ X0 @ sk_C) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C))),
% 0.18/0.50      inference('clc', [status(thm)], ['103', '104'])).
% 0.18/0.50  thf('106', plain,
% 0.18/0.50      (((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)
% 0.18/0.50        | ((sk_C) = (sk_D_1))
% 0.18/0.50        | (v2_struct_0 @ sk_A)
% 0.18/0.50        | (r1_tarski @ sk_D_1 @ sk_C))),
% 0.18/0.50      inference('sup-', [status(thm)], ['95', '105'])).
% 0.18/0.50  thf('107', plain,
% 0.18/0.50      ((~ (m1_orders_2 @ sk_C @ sk_A @ sk_D_1))
% 0.18/0.50         <= (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1)))),
% 0.18/0.50      inference('split', [status(esa)], ['2'])).
% 0.18/0.50  thf('108', plain, (~ ((m1_orders_2 @ sk_C @ sk_A @ sk_D_1))),
% 0.18/0.50      inference('sat_resolution*', [status(thm)], ['3', '80'])).
% 0.18/0.50  thf('109', plain, (~ (m1_orders_2 @ sk_C @ sk_A @ sk_D_1)),
% 0.18/0.50      inference('simpl_trail', [status(thm)], ['107', '108'])).
% 0.18/0.50  thf('110', plain,
% 0.18/0.50      (((r1_tarski @ sk_D_1 @ sk_C)
% 0.18/0.50        | (v2_struct_0 @ sk_A)
% 0.18/0.50        | ((sk_C) = (sk_D_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['106', '109'])).
% 0.18/0.50  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('112', plain, ((((sk_C) = (sk_D_1)) | (r1_tarski @ sk_D_1 @ sk_C))),
% 0.18/0.50      inference('clc', [status(thm)], ['110', '111'])).
% 0.18/0.50  thf(t60_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.18/0.50  thf('113', plain,
% 0.18/0.50      (![X3 : $i, X4 : $i]:
% 0.18/0.50         (~ (r1_tarski @ X3 @ X4) | ~ (r2_xboole_0 @ X4 @ X3))),
% 0.18/0.50      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.18/0.50  thf('114', plain, ((((sk_C) = (sk_D_1)) | ~ (r2_xboole_0 @ sk_C @ sk_D_1))),
% 0.18/0.50      inference('sup-', [status(thm)], ['112', '113'])).
% 0.18/0.50  thf('115', plain, ((r2_xboole_0 @ sk_C @ sk_D_1)),
% 0.18/0.50      inference('simpl_trail', [status(thm)], ['1', '82'])).
% 0.18/0.50  thf('116', plain, (((sk_C) = (sk_D_1))),
% 0.18/0.50      inference('demod', [status(thm)], ['114', '115'])).
% 0.18/0.50  thf('117', plain, ((r2_xboole_0 @ sk_C @ sk_C)),
% 0.18/0.50      inference('demod', [status(thm)], ['83', '116'])).
% 0.18/0.50  thf('118', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.18/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.18/0.50  thf('119', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.18/0.50      inference('simplify', [status(thm)], ['118'])).
% 0.18/0.50  thf('120', plain, ($false), inference('sup-', [status(thm)], ['117', '119'])).
% 0.18/0.50  
% 0.18/0.50  % SZS output end Refutation
% 0.18/0.50  
% 0.18/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
