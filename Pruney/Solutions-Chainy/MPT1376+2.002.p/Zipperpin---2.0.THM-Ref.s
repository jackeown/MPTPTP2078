%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D1DijdLDKW

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:43 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 908 expanded)
%              Number of leaves         :   19 ( 277 expanded)
%              Depth                    :   20
%              Number of atoms          : 2015 (13440 expanded)
%              Number of equality atoms :   43 ( 428 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t32_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tops_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
        <=> ( ( v1_tops_2 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_tops_2 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
          <=> ( ( v1_tops_2 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_compts_1])).

thf('0',plain,
    ( ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
    | ~ ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('9',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( g1_pre_topc @ X6 @ X7 )
       != ( g1_pre_topc @ X4 @ X5 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_tops_2 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('31',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('33',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('36',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('40',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('41',plain,
    ( ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('45',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('47',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('48',plain,
    ( ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('56',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('57',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( g1_pre_topc @ X6 @ X7 )
       != ( g1_pre_topc @ X4 @ X5 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['53','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('74',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        = ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','51','52'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['74','83'])).

thf('85',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ~ ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','84','85','86'])).

thf('88',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','87'])).

thf('89',plain,
    ( ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('92',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ sk_B @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      & ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('97',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('106',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('107',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_tops_2 @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('108',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( v1_tops_2 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('113',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('114',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( r1_tarski @ X8 @ ( u1_pre_topc @ X9 ) )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('115',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
      | ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('120',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
      | ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( v1_tops_2 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','120'])).

thf('122',plain,
    ( ~ ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('123',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
    | ( v1_tops_2 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['124'])).

thf('126',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('127',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('128',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','97','104','123','125','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D1DijdLDKW
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 383 iterations in 0.182s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.64  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.64  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(t32_compts_1, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( v1_tops_2 @ B @ A ) & 
% 0.46/0.64             ( m1_subset_1 @
% 0.46/0.64               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.46/0.64           ( ( v1_tops_2 @
% 0.46/0.64               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.46/0.64             ( m1_subset_1 @
% 0.46/0.64               B @ 
% 0.46/0.64               ( k1_zfmisc_1 @
% 0.46/0.64                 ( k1_zfmisc_1 @
% 0.46/0.64                   ( u1_struct_0 @
% 0.46/0.64                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.64            ( l1_pre_topc @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ( v1_tops_2 @ B @ A ) & 
% 0.46/0.64                ( m1_subset_1 @
% 0.46/0.64                  B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.46/0.64              ( ( v1_tops_2 @
% 0.46/0.64                  B @ 
% 0.46/0.64                  ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.46/0.64                ( m1_subset_1 @
% 0.46/0.64                  B @ 
% 0.46/0.64                  ( k1_zfmisc_1 @
% 0.46/0.64                    ( k1_zfmisc_1 @
% 0.46/0.64                      ( u1_struct_0 @
% 0.46/0.64                        ( g1_pre_topc @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t32_compts_1])).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (((v1_tops_2 @ sk_B @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64        | (v1_tops_2 @ sk_B @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.46/0.64       ((v1_tops_2 @ sk_B @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_B @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k1_zfmisc_1 @ 
% 0.46/0.64             (u1_struct_0 @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.46/0.64        | ~ (v1_tops_2 @ sk_B @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64        | ~ (m1_subset_1 @ sk_B @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.64        | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (~ ((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.46/0.64       ~
% 0.46/0.64       ((v1_tops_2 @ sk_B @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.46/0.64       ~
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 0.46/0.64       ~
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.46/0.64      inference('split', [status(esa)], ['2'])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (((v1_tops_2 @ sk_B @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((v1_tops_2 @ sk_B @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf(dt_u1_pre_topc, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_pre_topc @ A ) =>
% 0.46/0.64       ( m1_subset_1 @
% 0.46/0.64         ( u1_pre_topc @ A ) @ 
% 0.46/0.64         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X3 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.46/0.64          | ~ (l1_pre_topc @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.46/0.64  thf(dt_g1_pre_topc, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.64       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.46/0.64         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         ((v1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (v1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf(abstractness_v1_pre_topc, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_pre_topc @ A ) =>
% 0.46/0.64       ( ( v1_pre_topc @ A ) =>
% 0.46/0.64         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_pre_topc @ X0)
% 0.46/0.64          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X3 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.46/0.64          | ~ (l1_pre_topc @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.46/0.64  thf(free_g1_pre_topc, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.64       ( ![C:$i,D:$i]:
% 0.46/0.64         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.46/0.64           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.64         (((g1_pre_topc @ X6 @ X7) != (g1_pre_topc @ X4 @ X5))
% 0.46/0.64          | ((X6) = (X4))
% 0.46/0.64          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.46/0.64      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | ((u1_struct_0 @ X0) = (X1))
% 0.46/0.64          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.46/0.64              != (g1_pre_topc @ X1 @ X2)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.46/0.64          | ~ (l1_pre_topc @ X0)
% 0.46/0.64          | ~ (v1_pre_topc @ X0)
% 0.46/0.64          | ((u1_struct_0 @ X0) = (X2))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.46/0.64          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.46/0.64          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | ~ (l1_pre_topc @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64          | ((u1_struct_0 @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64              = (u1_struct_0 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X3 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.46/0.64          | ~ (l1_pre_topc @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         ((l1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (l1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64            = (u1_struct_0 @ X0))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['14', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.46/0.64        | (v1_tops_2 @ sk_B @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('split', [status(esa)], ['19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      ((((m1_subset_1 @ sk_B @ 
% 0.46/0.64          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['18', '20'])).
% 0.46/0.64  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64            = (u1_struct_0 @ X0))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['14', '17'])).
% 0.46/0.64  thf(t78_tops_2, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_pre_topc @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @
% 0.46/0.64             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.64           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X8 @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.46/0.64          | ~ (v1_tops_2 @ X8 @ X9)
% 0.46/0.64          | (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.46/0.64          | ~ (l1_pre_topc @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X1 @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.46/0.64          | ~ (l1_pre_topc @ X0)
% 0.46/0.64          | ~ (l1_pre_topc @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64          | (r1_tarski @ X1 @ 
% 0.46/0.64             (u1_pre_topc @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 0.46/0.64          | ~ (v1_tops_2 @ X1 @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (((~ (v1_tops_2 @ sk_B @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | (r1_tarski @ sk_B @ 
% 0.46/0.64            (u1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         | ~ (l1_pre_topc @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['23', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64            = (u1_struct_0 @ X0))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['14', '17'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('split', [status(esa)], ['19'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         ((v1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (((v1_pre_topc @ 
% 0.46/0.64         (g1_pre_topc @ 
% 0.46/0.64          (u1_struct_0 @ 
% 0.46/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.46/0.64          sk_B)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.46/0.64          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.46/0.64          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (((~ (l1_pre_topc @ 
% 0.46/0.64            (g1_pre_topc @ 
% 0.46/0.64             (u1_struct_0 @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.46/0.64             sk_B))
% 0.46/0.64         | ((u1_struct_0 @ 
% 0.46/0.64             (g1_pre_topc @ 
% 0.46/0.64              (u1_struct_0 @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.46/0.64              sk_B))
% 0.46/0.64             = (u1_struct_0 @ 
% 0.46/0.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('split', [status(esa)], ['19'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         ((l1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (((l1_pre_topc @ 
% 0.46/0.64         (g1_pre_topc @ 
% 0.46/0.64          (u1_struct_0 @ 
% 0.46/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.46/0.64          sk_B)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      ((((u1_struct_0 @ 
% 0.46/0.64          (g1_pre_topc @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.46/0.64           sk_B))
% 0.46/0.64          = (u1_struct_0 @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['33', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (((((u1_struct_0 @ (g1_pre_topc @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.46/0.64           = (u1_struct_0 @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['28', '37'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64            = (u1_struct_0 @ X0))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['14', '17'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (((v1_pre_topc @ 
% 0.46/0.64         (g1_pre_topc @ 
% 0.46/0.64          (u1_struct_0 @ 
% 0.46/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.46/0.64          sk_B)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      ((((v1_pre_topc @ (g1_pre_topc @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.46/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (((v1_pre_topc @ (g1_pre_topc @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.46/0.64          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.46/0.64          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (((~ (l1_pre_topc @ (g1_pre_topc @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.46/0.64         | ((u1_struct_0 @ (g1_pre_topc @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.46/0.64             = (u1_struct_0 @ sk_A))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64            = (u1_struct_0 @ X0))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['14', '17'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (((l1_pre_topc @ 
% 0.46/0.64         (g1_pre_topc @ 
% 0.46/0.64          (u1_struct_0 @ 
% 0.46/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.46/0.64          sk_B)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      ((((l1_pre_topc @ (g1_pre_topc @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.46/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (((l1_pre_topc @ (g1_pre_topc @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      ((((u1_struct_0 @ (g1_pre_topc @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.46/0.64          = (u1_struct_0 @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['45', '50'])).
% 0.46/0.64  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      ((((u1_struct_0 @ sk_A)
% 0.46/0.64          = (u1_struct_0 @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '51', '52'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (v1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_pre_topc @ X0)
% 0.46/0.64          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X3 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.46/0.64          | ~ (l1_pre_topc @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.64         (((g1_pre_topc @ X6 @ X7) != (g1_pre_topc @ X4 @ X5))
% 0.46/0.64          | ((X7) = (X5))
% 0.46/0.64          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.46/0.64      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | ((u1_pre_topc @ X0) = (X1))
% 0.46/0.64          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.46/0.64              != (g1_pre_topc @ X2 @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.46/0.64          | ~ (l1_pre_topc @ X0)
% 0.46/0.64          | ~ (v1_pre_topc @ X0)
% 0.46/0.64          | ((u1_pre_topc @ X0) = (X1))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['55', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         (((u1_pre_topc @ (g1_pre_topc @ X2 @ X1)) = (X1))
% 0.46/0.64          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.46/0.64          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['59'])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | ~ (l1_pre_topc @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64          | ((u1_pre_topc @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64              = (u1_pre_topc @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['54', '60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (l1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((u1_pre_topc @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64            = (u1_pre_topc @ X0))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (![X3 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.46/0.64          | ~ (l1_pre_topc @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k1_zfmisc_1 @ 
% 0.46/0.64             (u1_struct_0 @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.46/0.64          | ~ (l1_pre_topc @ X0)
% 0.46/0.64          | ~ (l1_pre_topc @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (l1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.46/0.64             (k1_zfmisc_1 @ 
% 0.46/0.64              (k1_zfmisc_1 @ 
% 0.46/0.64               (u1_struct_0 @ 
% 0.46/0.64                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))))),
% 0.46/0.64      inference('clc', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         ((v1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (v1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ 
% 0.46/0.64              (u1_struct_0 @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.46/0.64              (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      ((((v1_pre_topc @ 
% 0.46/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['53', '69'])).
% 0.46/0.64  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (((v1_pre_topc @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i]:
% 0.46/0.64         (((u1_pre_topc @ (g1_pre_topc @ X2 @ X1)) = (X1))
% 0.46/0.64          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.46/0.64          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['59'])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (((~ (l1_pre_topc @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | ((u1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64             = (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      ((((u1_struct_0 @ sk_A)
% 0.46/0.64          = (u1_struct_0 @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '51', '52'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((u1_pre_topc @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64            = (u1_pre_topc @ X0))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (l1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((l1_pre_topc @ 
% 0.46/0.64           (g1_pre_topc @ 
% 0.46/0.64            (u1_struct_0 @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.46/0.64            (u1_pre_topc @ X0)))
% 0.46/0.64          | ~ (l1_pre_topc @ X0)
% 0.46/0.64          | ~ (l1_pre_topc @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['76', '77'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (l1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X0)
% 0.46/0.64          | (l1_pre_topc @ 
% 0.46/0.64             (g1_pre_topc @ 
% 0.46/0.64              (u1_struct_0 @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.46/0.64              (u1_pre_topc @ X0))))),
% 0.46/0.64      inference('clc', [status(thm)], ['78', '79'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      ((((l1_pre_topc @ 
% 0.46/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['75', '80'])).
% 0.46/0.64  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (((l1_pre_topc @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      ((((u1_pre_topc @ 
% 0.46/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64          = (u1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['74', '83'])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (((l1_pre_topc @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.64  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((~ (v1_tops_2 @ sk_B @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '84', '85', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((v1_tops_2 @ sk_B @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.46/0.64             ((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['4', '87'])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      (((v1_tops_2 @ sk_B @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64        | (m1_subset_1 @ sk_B @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('split', [status(esa)], ['89'])).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X8 @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.46/0.64          | ~ (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.46/0.64          | (v1_tops_2 @ X8 @ X9)
% 0.46/0.64          | ~ (l1_pre_topc @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      (((~ (l1_pre_topc @ sk_A)
% 0.46/0.64         | (v1_tops_2 @ sk_B @ sk_A)
% 0.46/0.64         | ~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['90', '91'])).
% 0.46/0.64  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      ((((v1_tops_2 @ sk_B @ sk_A)
% 0.46/0.64         | ~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['92', '93'])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      (((v1_tops_2 @ sk_B @ sk_A))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) & 
% 0.46/0.64             ((v1_tops_2 @ sk_B @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.46/0.64             ((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['88', '94'])).
% 0.46/0.64  thf('96', plain,
% 0.46/0.64      ((~ (v1_tops_2 @ sk_B @ sk_A)) <= (~ ((v1_tops_2 @ sk_B @ sk_A)))),
% 0.46/0.64      inference('split', [status(esa)], ['2'])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      (((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.46/0.64       ~
% 0.46/0.64       ((v1_tops_2 @ sk_B @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.46/0.64       ~
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 0.46/0.64       ~
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['95', '96'])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('split', [status(esa)], ['89'])).
% 0.46/0.64  thf('99', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64            = (u1_struct_0 @ X0))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['14', '17'])).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_B @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k1_zfmisc_1 @ 
% 0.46/0.64             (u1_struct_0 @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('split', [status(esa)], ['2'])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      (((~ (m1_subset_1 @ sk_B @ 
% 0.46/0.64            (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.64  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_B @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['101', '102'])).
% 0.46/0.64  thf('104', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))) | 
% 0.46/0.64       ~
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['98', '103'])).
% 0.46/0.64  thf('105', plain,
% 0.46/0.64      (((v1_tops_2 @ sk_B @ sk_A)) <= (((v1_tops_2 @ sk_B @ sk_A)))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('split', [status(esa)], ['89'])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X8 @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.46/0.64          | ~ (v1_tops_2 @ X8 @ X9)
% 0.46/0.64          | (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.46/0.64          | ~ (l1_pre_topc @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      (((~ (l1_pre_topc @ sk_A)
% 0.46/0.64         | (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.46/0.64         | ~ (v1_tops_2 @ sk_B @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['106', '107'])).
% 0.46/0.64  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('110', plain,
% 0.46/0.64      ((((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.46/0.64         | ~ (v1_tops_2 @ sk_B @ sk_A)))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['108', '109'])).
% 0.46/0.64  thf('111', plain,
% 0.46/0.64      (((r1_tarski @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         <= (((v1_tops_2 @ sk_B @ sk_A)) & 
% 0.46/0.64             ((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['105', '110'])).
% 0.46/0.64  thf('112', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((u1_pre_topc @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.64            = (u1_pre_topc @ X0))
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf('113', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('split', [status(esa)], ['19'])).
% 0.46/0.64  thf('114', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X8 @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.46/0.64          | ~ (r1_tarski @ X8 @ (u1_pre_topc @ X9))
% 0.46/0.64          | (v1_tops_2 @ X8 @ X9)
% 0.46/0.64          | ~ (l1_pre_topc @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.46/0.64  thf('115', plain,
% 0.46/0.64      (((~ (l1_pre_topc @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | (v1_tops_2 @ sk_B @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | ~ (r1_tarski @ sk_B @ 
% 0.46/0.64              (u1_pre_topc @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['113', '114'])).
% 0.46/0.64  thf('116', plain,
% 0.46/0.64      (((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.46/0.64         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64         | (v1_tops_2 @ sk_B @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | ~ (l1_pre_topc @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['112', '115'])).
% 0.46/0.64  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('118', plain,
% 0.46/0.64      (((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.46/0.64         | (v1_tops_2 @ sk_B @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.46/0.64         | ~ (l1_pre_topc @ 
% 0.46/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['116', '117'])).
% 0.46/0.64  thf('119', plain,
% 0.46/0.64      (((l1_pre_topc @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.64  thf('120', plain,
% 0.46/0.64      (((~ (r1_tarski @ sk_B @ (u1_pre_topc @ sk_A))
% 0.46/0.64         | (v1_tops_2 @ sk_B @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.64  thf('121', plain,
% 0.46/0.64      (((v1_tops_2 @ sk_B @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (((v1_tops_2 @ sk_B @ sk_A)) & 
% 0.46/0.64             ((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) & 
% 0.46/0.64             ((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['111', '120'])).
% 0.46/0.64  thf('122', plain,
% 0.46/0.64      ((~ (v1_tops_2 @ sk_B @ 
% 0.46/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((v1_tops_2 @ sk_B @ 
% 0.46/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.46/0.64      inference('split', [status(esa)], ['2'])).
% 0.46/0.64  thf('123', plain,
% 0.46/0.64      (~ ((v1_tops_2 @ sk_B @ sk_A)) | 
% 0.46/0.64       ((v1_tops_2 @ sk_B @ 
% 0.46/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.46/0.64       ~
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 0.46/0.64       ~
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['121', '122'])).
% 0.46/0.64  thf('124', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.46/0.64        | (m1_subset_1 @ sk_B @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('125', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))) | 
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.64      inference('split', [status(esa)], ['124'])).
% 0.46/0.64  thf('126', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k1_zfmisc_1 @ 
% 0.46/0.64                 (u1_struct_0 @ 
% 0.46/0.64                  (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('127', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_B @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_B @ 
% 0.46/0.64               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.46/0.64      inference('split', [status(esa)], ['2'])).
% 0.46/0.64  thf('128', plain,
% 0.46/0.64      (~
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k1_zfmisc_1 @ 
% 0.46/0.64           (u1_struct_0 @ 
% 0.46/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))) | 
% 0.46/0.64       ((m1_subset_1 @ sk_B @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['126', '127'])).
% 0.46/0.64  thf('129', plain, ($false),
% 0.46/0.64      inference('sat_resolution*', [status(thm)],
% 0.46/0.64                ['1', '3', '97', '104', '123', '125', '128'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
