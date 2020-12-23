%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZlKZs6kMf7

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:05 EST 2020

% Result     : Theorem 7.85s
% Output     : Refutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :  267 (1688 expanded)
%              Number of leaves         :   55 ( 539 expanded)
%              Depth                    :   24
%              Number of atoms          : 2484 (16466 expanded)
%              Number of equality atoms :  134 ( 938 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t54_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
            <=> ? [D: $i] :
                  ( ( r2_hidden @ B @ D )
                  & ( r1_tarski @ D @ C )
                  & ( v3_pre_topc @ D @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_tops_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X67: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X67 @ sk_A )
      | ~ ( r1_tarski @ X67 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X67 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X67: $i] :
        ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X67 @ sk_A )
        | ~ ( r1_tarski @ X67 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X67 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( l1_pre_topc @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X58 @ X59 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ! [X67: $i] :
        ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X67 @ sk_A )
        | ~ ( r1_tarski @ X67 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X67 ) )
   <= ! [X67: $i] :
        ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X67 @ sk_A )
        | ~ ( r1_tarski @ X67 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X67 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X67: $i] :
        ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X67 @ sk_A )
        | ~ ( r1_tarski @ X67 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X67 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('17',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X63 @ X62 ) @ X62 )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('22',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X60 @ X61 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('23',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ! [X67: $i] :
        ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X67 @ sk_A )
        | ~ ( r1_tarski @ X67 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X67 ) ) ),
    inference(demod,[status(thm)],['15','20','26'])).

thf('28',plain,
    ( ~ ! [X67: $i] :
          ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X67 @ sk_A )
          | ~ ( r1_tarski @ X67 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X67 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','27'])).

thf('29',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( u1_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('35',plain,
    ( ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('37',plain,(
    ! [X53: $i] :
      ( ( l1_struct_0 @ X53 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( u1_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t53_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( v3_pre_topc @ X54 @ X55 )
      | ( ( k2_pre_topc @ X55 @ ( k7_subset_1 @ ( u1_struct_0 @ X55 ) @ ( k2_struct_0 @ X55 ) @ X54 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X55 ) @ ( k2_struct_0 @ X55 ) @ X54 ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t53_pre_topc])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ~ ( v3_pre_topc @ sk_D @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('46',plain,
    ( ( ~ ( v3_pre_topc @ sk_D @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( u1_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('50',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k3_subset_1 @ X46 @ ( k7_subset_1 @ X46 @ X47 @ X45 ) )
        = ( k4_subset_1 @ X46 @ ( k3_subset_1 @ X46 @ X47 ) @ X45 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_C_1 ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X42 @ X44 )
        = ( k4_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('57',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['59'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_xboole_0 @ X22 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('64',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 = X18 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( ( k2_xboole_0 @ X20 @ X18 )
       != ( k2_xboole_0 @ X19 @ X21 ) )
      | ~ ( r1_xboole_0 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('68',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30 != X29 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X29 ) )
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('74',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X29 ) )
     != ( k1_tarski @ X29 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('75',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('78',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X29: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X29 ) ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['72','80'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('82',plain,(
    ! [X32: $i] :
      ( r1_tarski @ ( k1_tarski @ X32 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('86',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( m1_subset_1 @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('88',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('90',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('95',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('96',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( u1_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('104',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('106',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( u1_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('110',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('113',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['106','113'])).

thf('115',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','55','91','94','99','114'])).

thf('116',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('118',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('120',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('121',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k3_subset_1 @ X46 @ ( k7_subset_1 @ X46 @ X47 @ X45 ) )
        = ( k4_subset_1 @ X46 @ ( k3_subset_1 @ X46 @ X47 ) @ X45 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) )
        = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 @ sk_C_1 ) )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('125',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X42 @ X44 )
        = ( k4_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('130',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['123','126','127','128','129'])).

thf('131',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['118','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('133',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X42 @ X44 )
        = ( k4_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('136',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('137',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['118','130'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('140',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('141',plain,
    ( ( ~ ( v3_pre_topc @ sk_D @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','131','134','137','138','139','140'])).

thf('142',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','141'])).

thf('143',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('144',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( u1_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('145',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( ( k1_tops_1 @ X57 @ X56 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X57 ) @ ( k2_pre_topc @ X57 @ ( k3_subset_1 @ ( u1_struct_0 @ X57 ) @ X56 ) ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['143','146'])).

thf('148',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('149',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( u1_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('150',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('151',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('152',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['149','152'])).

thf('154',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('155',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['148','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('159',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['147','156','157','158'])).

thf('160',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['118','130'])).

thf('161',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['142','161'])).

thf('163',plain,(
    ! [X52: $i] :
      ( ( ( k2_struct_0 @ X52 )
        = ( u1_struct_0 @ X52 ) )
      | ~ ( l1_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('165',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('166',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k3_subset_1 @ X46 @ ( k7_subset_1 @ X46 @ X47 @ X45 ) )
        = ( k4_subset_1 @ X46 @ ( k3_subset_1 @ X46 @ X47 ) @ X45 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('167',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D ) )
          = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('170',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('171',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['148','155'])).

thf('172',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('174',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('175',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('176',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('179',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('180',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 = X18 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( ( k2_xboole_0 @ X20 @ X18 )
       != ( k2_xboole_0 @ X19 @ X21 ) )
      | ~ ( r1_xboole_0 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
       != X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('185',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['182','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['178','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['177','187'])).

thf('189',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_D )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['174','188'])).

thf('190',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['168','169','172','173','189'])).

thf('191',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = sk_D )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['163','190'])).

thf('192',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('193',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = sk_D )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['162','193'])).

thf('195',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('196',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('198',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( r1_tarski @ X64 @ X66 )
      | ( r1_tarski @ ( k1_tops_1 @ X65 @ X64 ) @ ( k1_tops_1 @ X65 @ X66 ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('199',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['196','201'])).

thf('203',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['195','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('205',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['194','205'])).

thf('207',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','206'])).

thf('208',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('209',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','28','30','209'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZlKZs6kMf7
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 7.85/8.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.85/8.03  % Solved by: fo/fo7.sh
% 7.85/8.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.85/8.03  % done 15792 iterations in 7.610s
% 7.85/8.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.85/8.03  % SZS output start Refutation
% 7.85/8.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.85/8.03  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 7.85/8.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.85/8.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.85/8.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.85/8.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.85/8.03  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 7.85/8.03  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.85/8.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.85/8.03  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.85/8.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.85/8.03  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 7.85/8.03  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 7.85/8.03  thf(sk_A_type, type, sk_A: $i).
% 7.85/8.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.85/8.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.85/8.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.85/8.03  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 7.85/8.03  thf(sk_D_type, type, sk_D: $i).
% 7.85/8.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.85/8.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.85/8.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.85/8.03  thf(sk_B_type, type, sk_B: $i).
% 7.85/8.03  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 7.85/8.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.85/8.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.85/8.03  thf(t54_tops_1, conjecture,
% 7.85/8.03    (![A:$i]:
% 7.85/8.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.85/8.03       ( ![B:$i,C:$i]:
% 7.85/8.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.85/8.03           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 7.85/8.03             ( ?[D:$i]:
% 7.85/8.03               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 7.85/8.03                 ( v3_pre_topc @ D @ A ) & 
% 7.85/8.03                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 7.85/8.03  thf(zf_stmt_0, negated_conjecture,
% 7.85/8.03    (~( ![A:$i]:
% 7.85/8.03        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.85/8.03          ( ![B:$i,C:$i]:
% 7.85/8.03            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.85/8.03              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 7.85/8.03                ( ?[D:$i]:
% 7.85/8.03                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 7.85/8.03                    ( v3_pre_topc @ D @ A ) & 
% 7.85/8.03                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 7.85/8.03    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 7.85/8.03  thf('0', plain,
% 7.85/8.03      (((r2_hidden @ sk_B @ sk_D)
% 7.85/8.03        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.03  thf('1', plain,
% 7.85/8.03      (((r2_hidden @ sk_B @ sk_D)) | 
% 7.85/8.03       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.03      inference('split', [status(esa)], ['0'])).
% 7.85/8.03  thf('2', plain,
% 7.85/8.03      (((r1_tarski @ sk_D @ sk_C_1)
% 7.85/8.03        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.03  thf('3', plain,
% 7.85/8.03      (((r1_tarski @ sk_D @ sk_C_1)) | 
% 7.85/8.03       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.03      inference('split', [status(esa)], ['2'])).
% 7.85/8.03  thf('4', plain,
% 7.85/8.03      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.03        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.03  thf('5', plain,
% 7.85/8.03      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 7.85/8.03       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.03      inference('split', [status(esa)], ['4'])).
% 7.85/8.03  thf('6', plain,
% 7.85/8.03      (![X67 : $i]:
% 7.85/8.03         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.03          | ~ (v3_pre_topc @ X67 @ sk_A)
% 7.85/8.03          | ~ (r1_tarski @ X67 @ sk_C_1)
% 7.85/8.03          | ~ (r2_hidden @ sk_B @ X67)
% 7.85/8.03          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.03  thf('7', plain,
% 7.85/8.03      ((![X67 : $i]:
% 7.85/8.03          (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.03           | ~ (v3_pre_topc @ X67 @ sk_A)
% 7.85/8.03           | ~ (r1_tarski @ X67 @ sk_C_1)
% 7.85/8.03           | ~ (r2_hidden @ sk_B @ X67))) | 
% 7.85/8.03       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.03      inference('split', [status(esa)], ['6'])).
% 7.85/8.03  thf('8', plain,
% 7.85/8.03      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 7.85/8.03         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 7.85/8.03      inference('split', [status(esa)], ['0'])).
% 7.85/8.03  thf('9', plain,
% 7.85/8.03      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.03  thf(dt_k1_tops_1, axiom,
% 7.85/8.03    (![A:$i,B:$i]:
% 7.85/8.03     ( ( ( l1_pre_topc @ A ) & 
% 7.85/8.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.85/8.03       ( m1_subset_1 @
% 7.85/8.03         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.85/8.03  thf('10', plain,
% 7.85/8.03      (![X58 : $i, X59 : $i]:
% 7.85/8.03         (~ (l1_pre_topc @ X58)
% 7.85/8.03          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 7.85/8.03          | (m1_subset_1 @ (k1_tops_1 @ X58 @ X59) @ 
% 7.85/8.03             (k1_zfmisc_1 @ (u1_struct_0 @ X58))))),
% 7.85/8.04      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 7.85/8.04  thf('11', plain,
% 7.85/8.04      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 7.85/8.04         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04        | ~ (l1_pre_topc @ sk_A))),
% 7.85/8.04      inference('sup-', [status(thm)], ['9', '10'])).
% 7.85/8.04  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('13', plain,
% 7.85/8.04      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 7.85/8.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.04      inference('demod', [status(thm)], ['11', '12'])).
% 7.85/8.04  thf('14', plain,
% 7.85/8.04      ((![X67 : $i]:
% 7.85/8.04          (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04           | ~ (v3_pre_topc @ X67 @ sk_A)
% 7.85/8.04           | ~ (r1_tarski @ X67 @ sk_C_1)
% 7.85/8.04           | ~ (r2_hidden @ sk_B @ X67)))
% 7.85/8.04         <= ((![X67 : $i]:
% 7.85/8.04                (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04                 | ~ (v3_pre_topc @ X67 @ sk_A)
% 7.85/8.04                 | ~ (r1_tarski @ X67 @ sk_C_1)
% 7.85/8.04                 | ~ (r2_hidden @ sk_B @ X67))))),
% 7.85/8.04      inference('split', [status(esa)], ['6'])).
% 7.85/8.04  thf('15', plain,
% 7.85/8.04      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 7.85/8.04         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 7.85/8.04         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 7.85/8.04         <= ((![X67 : $i]:
% 7.85/8.04                (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04                 | ~ (v3_pre_topc @ X67 @ sk_A)
% 7.85/8.04                 | ~ (r1_tarski @ X67 @ sk_C_1)
% 7.85/8.04                 | ~ (r2_hidden @ sk_B @ X67))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['13', '14'])).
% 7.85/8.04  thf('16', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf(t44_tops_1, axiom,
% 7.85/8.04    (![A:$i]:
% 7.85/8.04     ( ( l1_pre_topc @ A ) =>
% 7.85/8.04       ( ![B:$i]:
% 7.85/8.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.85/8.04           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 7.85/8.04  thf('17', plain,
% 7.85/8.04      (![X62 : $i, X63 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 7.85/8.04          | (r1_tarski @ (k1_tops_1 @ X63 @ X62) @ X62)
% 7.85/8.04          | ~ (l1_pre_topc @ X63))),
% 7.85/8.04      inference('cnf', [status(esa)], [t44_tops_1])).
% 7.85/8.04  thf('18', plain,
% 7.85/8.04      ((~ (l1_pre_topc @ sk_A)
% 7.85/8.04        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 7.85/8.04      inference('sup-', [status(thm)], ['16', '17'])).
% 7.85/8.04  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('20', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 7.85/8.04      inference('demod', [status(thm)], ['18', '19'])).
% 7.85/8.04  thf('21', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf(fc9_tops_1, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 7.85/8.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.85/8.04       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 7.85/8.04  thf('22', plain,
% 7.85/8.04      (![X60 : $i, X61 : $i]:
% 7.85/8.04         (~ (l1_pre_topc @ X60)
% 7.85/8.04          | ~ (v2_pre_topc @ X60)
% 7.85/8.04          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 7.85/8.04          | (v3_pre_topc @ (k1_tops_1 @ X60 @ X61) @ X60))),
% 7.85/8.04      inference('cnf', [status(esa)], [fc9_tops_1])).
% 7.85/8.04  thf('23', plain,
% 7.85/8.04      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 7.85/8.04        | ~ (v2_pre_topc @ sk_A)
% 7.85/8.04        | ~ (l1_pre_topc @ sk_A))),
% 7.85/8.04      inference('sup-', [status(thm)], ['21', '22'])).
% 7.85/8.04  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('26', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 7.85/8.04      inference('demod', [status(thm)], ['23', '24', '25'])).
% 7.85/8.04  thf('27', plain,
% 7.85/8.04      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 7.85/8.04         <= ((![X67 : $i]:
% 7.85/8.04                (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04                 | ~ (v3_pre_topc @ X67 @ sk_A)
% 7.85/8.04                 | ~ (r1_tarski @ X67 @ sk_C_1)
% 7.85/8.04                 | ~ (r2_hidden @ sk_B @ X67))))),
% 7.85/8.04      inference('demod', [status(thm)], ['15', '20', '26'])).
% 7.85/8.04  thf('28', plain,
% 7.85/8.04      (~
% 7.85/8.04       (![X67 : $i]:
% 7.85/8.04          (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04           | ~ (v3_pre_topc @ X67 @ sk_A)
% 7.85/8.04           | ~ (r1_tarski @ X67 @ sk_C_1)
% 7.85/8.04           | ~ (r2_hidden @ sk_B @ X67))) | 
% 7.85/8.04       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['8', '27'])).
% 7.85/8.04  thf('29', plain,
% 7.85/8.04      (((v3_pre_topc @ sk_D @ sk_A)
% 7.85/8.04        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('30', plain,
% 7.85/8.04      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 7.85/8.04       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.04      inference('split', [status(esa)], ['29'])).
% 7.85/8.04  thf('31', plain,
% 7.85/8.04      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 7.85/8.04      inference('split', [status(esa)], ['0'])).
% 7.85/8.04  thf('32', plain,
% 7.85/8.04      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 7.85/8.04      inference('split', [status(esa)], ['29'])).
% 7.85/8.04  thf(d3_struct_0, axiom,
% 7.85/8.04    (![A:$i]:
% 7.85/8.04     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 7.85/8.04  thf('33', plain,
% 7.85/8.04      (![X52 : $i]:
% 7.85/8.04         (((k2_struct_0 @ X52) = (u1_struct_0 @ X52)) | ~ (l1_struct_0 @ X52))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.85/8.04  thf('34', plain,
% 7.85/8.04      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('split', [status(esa)], ['4'])).
% 7.85/8.04  thf('35', plain,
% 7.85/8.04      ((((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.85/8.04         | ~ (l1_struct_0 @ sk_A)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup+', [status(thm)], ['33', '34'])).
% 7.85/8.04  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf(dt_l1_pre_topc, axiom,
% 7.85/8.04    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 7.85/8.04  thf('37', plain,
% 7.85/8.04      (![X53 : $i]: ((l1_struct_0 @ X53) | ~ (l1_pre_topc @ X53))),
% 7.85/8.04      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 7.85/8.04  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 7.85/8.04      inference('sup-', [status(thm)], ['36', '37'])).
% 7.85/8.04  thf('39', plain,
% 7.85/8.04      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['35', '38'])).
% 7.85/8.04  thf('40', plain,
% 7.85/8.04      (![X52 : $i]:
% 7.85/8.04         (((k2_struct_0 @ X52) = (u1_struct_0 @ X52)) | ~ (l1_struct_0 @ X52))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.85/8.04  thf(t53_pre_topc, axiom,
% 7.85/8.04    (![A:$i]:
% 7.85/8.04     ( ( l1_pre_topc @ A ) =>
% 7.85/8.04       ( ![B:$i]:
% 7.85/8.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.85/8.04           ( ( ( v3_pre_topc @ B @ A ) =>
% 7.85/8.04               ( ( k2_pre_topc @
% 7.85/8.04                   A @ 
% 7.85/8.04                   ( k7_subset_1 @
% 7.85/8.04                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 7.85/8.04                 ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) & 
% 7.85/8.04             ( ( ( v2_pre_topc @ A ) & 
% 7.85/8.04                 ( ( k2_pre_topc @
% 7.85/8.04                     A @ 
% 7.85/8.04                     ( k7_subset_1 @
% 7.85/8.04                       ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 7.85/8.04                   ( k7_subset_1 @
% 7.85/8.04                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) =>
% 7.85/8.04               ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 7.85/8.04  thf('41', plain,
% 7.85/8.04      (![X54 : $i, X55 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 7.85/8.04          | ~ (v3_pre_topc @ X54 @ X55)
% 7.85/8.04          | ((k2_pre_topc @ X55 @ 
% 7.85/8.04              (k7_subset_1 @ (u1_struct_0 @ X55) @ (k2_struct_0 @ X55) @ X54))
% 7.85/8.04              = (k7_subset_1 @ (u1_struct_0 @ X55) @ (k2_struct_0 @ X55) @ X54))
% 7.85/8.04          | ~ (l1_pre_topc @ X55))),
% 7.85/8.04      inference('cnf', [status(esa)], [t53_pre_topc])).
% 7.85/8.04  thf('42', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 7.85/8.04          | ~ (l1_struct_0 @ X0)
% 7.85/8.04          | ~ (l1_pre_topc @ X0)
% 7.85/8.04          | ((k2_pre_topc @ X0 @ 
% 7.85/8.04              (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1))
% 7.85/8.04              = (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1))
% 7.85/8.04          | ~ (v3_pre_topc @ X1 @ X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['40', '41'])).
% 7.85/8.04  thf('43', plain,
% 7.85/8.04      (((~ (v3_pre_topc @ sk_D @ sk_A)
% 7.85/8.04         | ((k2_pre_topc @ sk_A @ 
% 7.85/8.04             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_D))
% 7.85/8.04             = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04                sk_D))
% 7.85/8.04         | ~ (l1_pre_topc @ sk_A)
% 7.85/8.04         | ~ (l1_struct_0 @ sk_A)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['39', '42'])).
% 7.85/8.04  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 7.85/8.04      inference('sup-', [status(thm)], ['36', '37'])).
% 7.85/8.04  thf('46', plain,
% 7.85/8.04      (((~ (v3_pre_topc @ sk_D @ sk_A)
% 7.85/8.04         | ((k2_pre_topc @ sk_A @ 
% 7.85/8.04             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_D))
% 7.85/8.04             = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04                sk_D))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['43', '44', '45'])).
% 7.85/8.04  thf('47', plain,
% 7.85/8.04      (![X52 : $i]:
% 7.85/8.04         (((k2_struct_0 @ X52) = (u1_struct_0 @ X52)) | ~ (l1_struct_0 @ X52))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.85/8.04  thf('48', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('49', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf(t33_subset_1, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.85/8.04       ( ![C:$i]:
% 7.85/8.04         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.85/8.04           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 7.85/8.04             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 7.85/8.04  thf('50', plain,
% 7.85/8.04      (![X45 : $i, X46 : $i, X47 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 7.85/8.04          | ((k3_subset_1 @ X46 @ (k7_subset_1 @ X46 @ X47 @ X45))
% 7.85/8.04              = (k4_subset_1 @ X46 @ (k3_subset_1 @ X46 @ X47) @ X45))
% 7.85/8.04          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46)))),
% 7.85/8.04      inference('cnf', [status(esa)], [t33_subset_1])).
% 7.85/8.04  thf('51', plain,
% 7.85/8.04      (![X0 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1))
% 7.85/8.04              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_C_1)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['49', '50'])).
% 7.85/8.04  thf('52', plain,
% 7.85/8.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_C_1))
% 7.85/8.04         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 7.85/8.04      inference('sup-', [status(thm)], ['48', '51'])).
% 7.85/8.04  thf('53', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf(redefinition_k7_subset_1, axiom,
% 7.85/8.04    (![A:$i,B:$i,C:$i]:
% 7.85/8.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.85/8.04       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 7.85/8.04  thf('54', plain,
% 7.85/8.04      (![X42 : $i, X43 : $i, X44 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 7.85/8.04          | ((k7_subset_1 @ X43 @ X42 @ X44) = (k4_xboole_0 @ X42 @ X44)))),
% 7.85/8.04      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 7.85/8.04  thf('55', plain,
% 7.85/8.04      (![X0 : $i]:
% 7.85/8.04         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 7.85/8.04           = (k4_xboole_0 @ sk_C_1 @ X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['53', '54'])).
% 7.85/8.04  thf(l27_zfmisc_1, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 7.85/8.04  thf('56', plain,
% 7.85/8.04      (![X27 : $i, X28 : $i]:
% 7.85/8.04         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 7.85/8.04      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 7.85/8.04  thf(t88_xboole_1, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( r1_xboole_0 @ A @ B ) =>
% 7.85/8.04       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 7.85/8.04  thf('57', plain,
% 7.85/8.04      (![X25 : $i, X26 : $i]:
% 7.85/8.04         (((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ X26) = (X25))
% 7.85/8.04          | ~ (r1_xboole_0 @ X25 @ X26))),
% 7.85/8.04      inference('cnf', [status(esa)], [t88_xboole_1])).
% 7.85/8.04  thf('58', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         ((r2_hidden @ X1 @ X0)
% 7.85/8.04          | ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X0)
% 7.85/8.04              = (k1_tarski @ X1)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['56', '57'])).
% 7.85/8.04  thf(d10_xboole_0, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.85/8.04  thf('59', plain,
% 7.85/8.04      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 7.85/8.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.85/8.04  thf('60', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 7.85/8.04      inference('simplify', [status(thm)], ['59'])).
% 7.85/8.04  thf(t85_xboole_1, axiom,
% 7.85/8.04    (![A:$i,B:$i,C:$i]:
% 7.85/8.04     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 7.85/8.04  thf('61', plain,
% 7.85/8.04      (![X22 : $i, X23 : $i, X24 : $i]:
% 7.85/8.04         (~ (r1_tarski @ X22 @ X23)
% 7.85/8.04          | (r1_xboole_0 @ X22 @ (k4_xboole_0 @ X24 @ X23)))),
% 7.85/8.04      inference('cnf', [status(esa)], [t85_xboole_1])).
% 7.85/8.04  thf('62', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['60', '61'])).
% 7.85/8.04  thf('63', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 7.85/8.04      inference('sup+', [status(thm)], ['58', '62'])).
% 7.85/8.04  thf(t1_boole, axiom,
% 7.85/8.04    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.85/8.04  thf('64', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 7.85/8.04      inference('cnf', [status(esa)], [t1_boole])).
% 7.85/8.04  thf('65', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 7.85/8.04      inference('cnf', [status(esa)], [t1_boole])).
% 7.85/8.04  thf(t72_xboole_1, axiom,
% 7.85/8.04    (![A:$i,B:$i,C:$i,D:$i]:
% 7.85/8.04     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 7.85/8.04         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 7.85/8.04       ( ( C ) = ( B ) ) ))).
% 7.85/8.04  thf('66', plain,
% 7.85/8.04      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 7.85/8.04         (((X19) = (X18))
% 7.85/8.04          | ~ (r1_xboole_0 @ X19 @ X20)
% 7.85/8.04          | ((k2_xboole_0 @ X20 @ X18) != (k2_xboole_0 @ X19 @ X21))
% 7.85/8.04          | ~ (r1_xboole_0 @ X21 @ X18))),
% 7.85/8.04      inference('cnf', [status(esa)], [t72_xboole_1])).
% 7.85/8.04  thf('67', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.85/8.04         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 7.85/8.04          | ~ (r1_xboole_0 @ X1 @ k1_xboole_0)
% 7.85/8.04          | ~ (r1_xboole_0 @ X2 @ X0)
% 7.85/8.04          | ((X2) = (k1_xboole_0)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['65', '66'])).
% 7.85/8.04  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 7.85/8.04  thf('68', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 7.85/8.04      inference('cnf', [status(esa)], [t65_xboole_1])).
% 7.85/8.04  thf('69', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.85/8.04         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 7.85/8.04          | ~ (r1_xboole_0 @ X2 @ X0)
% 7.85/8.04          | ((X2) = (k1_xboole_0)))),
% 7.85/8.04      inference('demod', [status(thm)], ['67', '68'])).
% 7.85/8.04  thf('70', plain,
% 7.85/8.04      (![X1 : $i, X2 : $i]:
% 7.85/8.04         (((X2) = (k1_xboole_0))
% 7.85/8.04          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X1)))),
% 7.85/8.04      inference('simplify', [status(thm)], ['69'])).
% 7.85/8.04  thf('71', plain,
% 7.85/8.04      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['64', '70'])).
% 7.85/8.04  thf('72', plain,
% 7.85/8.04      (![X0 : $i]:
% 7.85/8.04         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 7.85/8.04          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['63', '71'])).
% 7.85/8.04  thf(t20_zfmisc_1, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 7.85/8.04         ( k1_tarski @ A ) ) <=>
% 7.85/8.04       ( ( A ) != ( B ) ) ))).
% 7.85/8.04  thf('73', plain,
% 7.85/8.04      (![X29 : $i, X30 : $i]:
% 7.85/8.04         (((X30) != (X29))
% 7.85/8.04          | ((k4_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X29))
% 7.85/8.04              != (k1_tarski @ X30)))),
% 7.85/8.04      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 7.85/8.04  thf('74', plain,
% 7.85/8.04      (![X29 : $i]:
% 7.85/8.04         ((k4_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X29))
% 7.85/8.04           != (k1_tarski @ X29))),
% 7.85/8.04      inference('simplify', [status(thm)], ['73'])).
% 7.85/8.04  thf(t3_boole, axiom,
% 7.85/8.04    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.85/8.04  thf('75', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 7.85/8.04      inference('cnf', [status(esa)], [t3_boole])).
% 7.85/8.04  thf(t48_xboole_1, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.85/8.04  thf('76', plain,
% 7.85/8.04      (![X12 : $i, X13 : $i]:
% 7.85/8.04         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 7.85/8.04           = (k3_xboole_0 @ X12 @ X13))),
% 7.85/8.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.85/8.04  thf('77', plain,
% 7.85/8.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 7.85/8.04      inference('sup+', [status(thm)], ['75', '76'])).
% 7.85/8.04  thf(t2_boole, axiom,
% 7.85/8.04    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 7.85/8.04  thf('78', plain,
% 7.85/8.04      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 7.85/8.04      inference('cnf', [status(esa)], [t2_boole])).
% 7.85/8.04  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.85/8.04      inference('demod', [status(thm)], ['77', '78'])).
% 7.85/8.04  thf('80', plain, (![X29 : $i]: ((k1_xboole_0) != (k1_tarski @ X29))),
% 7.85/8.04      inference('demod', [status(thm)], ['74', '79'])).
% 7.85/8.04  thf('81', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 7.85/8.04      inference('clc', [status(thm)], ['72', '80'])).
% 7.85/8.04  thf(t80_zfmisc_1, axiom,
% 7.85/8.04    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 7.85/8.04  thf('82', plain,
% 7.85/8.04      (![X32 : $i]: (r1_tarski @ (k1_tarski @ X32) @ (k1_zfmisc_1 @ X32))),
% 7.85/8.04      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 7.85/8.04  thf(d3_tarski, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( r1_tarski @ A @ B ) <=>
% 7.85/8.04       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.85/8.04  thf('83', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.85/8.04         (~ (r2_hidden @ X0 @ X1)
% 7.85/8.04          | (r2_hidden @ X0 @ X2)
% 7.85/8.04          | ~ (r1_tarski @ X1 @ X2))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_tarski])).
% 7.85/8.04  thf('84', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 7.85/8.04          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['82', '83'])).
% 7.85/8.04  thf('85', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['81', '84'])).
% 7.85/8.04  thf(d2_subset_1, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( ( v1_xboole_0 @ A ) =>
% 7.85/8.04         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 7.85/8.04       ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.85/8.04         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 7.85/8.04  thf('86', plain,
% 7.85/8.04      (![X33 : $i, X34 : $i]:
% 7.85/8.04         (~ (r2_hidden @ X33 @ X34)
% 7.85/8.04          | (m1_subset_1 @ X33 @ X34)
% 7.85/8.04          | (v1_xboole_0 @ X34))),
% 7.85/8.04      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.85/8.04  thf('87', plain,
% 7.85/8.04      (![X0 : $i]:
% 7.85/8.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 7.85/8.04          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['85', '86'])).
% 7.85/8.04  thf(fc1_subset_1, axiom,
% 7.85/8.04    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.85/8.04  thf('88', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 7.85/8.04      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.85/8.04  thf('89', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.85/8.04      inference('clc', [status(thm)], ['87', '88'])).
% 7.85/8.04  thf(d5_subset_1, axiom,
% 7.85/8.04    (![A:$i,B:$i]:
% 7.85/8.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.85/8.04       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 7.85/8.04  thf('90', plain,
% 7.85/8.04      (![X36 : $i, X37 : $i]:
% 7.85/8.04         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 7.85/8.04          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 7.85/8.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.85/8.04  thf('91', plain,
% 7.85/8.04      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['89', '90'])).
% 7.85/8.04  thf('92', plain,
% 7.85/8.04      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['89', '90'])).
% 7.85/8.04  thf('93', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.85/8.04      inference('demod', [status(thm)], ['77', '78'])).
% 7.85/8.04  thf('94', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 7.85/8.04      inference('sup+', [status(thm)], ['92', '93'])).
% 7.85/8.04  thf(t4_subset_1, axiom,
% 7.85/8.04    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 7.85/8.04  thf('95', plain,
% 7.85/8.04      (![X48 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 7.85/8.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.85/8.04  thf('96', plain,
% 7.85/8.04      (![X36 : $i, X37 : $i]:
% 7.85/8.04         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 7.85/8.04          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 7.85/8.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.85/8.04  thf('97', plain,
% 7.85/8.04      (![X0 : $i]:
% 7.85/8.04         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['95', '96'])).
% 7.85/8.04  thf('98', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 7.85/8.04      inference('cnf', [status(esa)], [t3_boole])).
% 7.85/8.04  thf('99', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 7.85/8.04      inference('sup+', [status(thm)], ['97', '98'])).
% 7.85/8.04  thf('100', plain,
% 7.85/8.04      (![X52 : $i]:
% 7.85/8.04         (((k2_struct_0 @ X52) = (u1_struct_0 @ X52)) | ~ (l1_struct_0 @ X52))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.85/8.04  thf('101', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('102', plain,
% 7.85/8.04      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.85/8.04        | ~ (l1_struct_0 @ sk_A))),
% 7.85/8.04      inference('sup+', [status(thm)], ['100', '101'])).
% 7.85/8.04  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 7.85/8.04      inference('sup-', [status(thm)], ['36', '37'])).
% 7.85/8.04  thf('104', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.85/8.04      inference('demod', [status(thm)], ['102', '103'])).
% 7.85/8.04  thf('105', plain,
% 7.85/8.04      (![X36 : $i, X37 : $i]:
% 7.85/8.04         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 7.85/8.04          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 7.85/8.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.85/8.04  thf('106', plain,
% 7.85/8.04      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1)
% 7.85/8.04         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))),
% 7.85/8.04      inference('sup-', [status(thm)], ['104', '105'])).
% 7.85/8.04  thf('107', plain,
% 7.85/8.04      (![X52 : $i]:
% 7.85/8.04         (((k2_struct_0 @ X52) = (u1_struct_0 @ X52)) | ~ (l1_struct_0 @ X52))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.85/8.04  thf('108', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('109', plain,
% 7.85/8.04      (![X36 : $i, X37 : $i]:
% 7.85/8.04         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 7.85/8.04          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 7.85/8.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.85/8.04  thf('110', plain,
% 7.85/8.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 7.85/8.04         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 7.85/8.04      inference('sup-', [status(thm)], ['108', '109'])).
% 7.85/8.04  thf('111', plain,
% 7.85/8.04      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 7.85/8.04          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))
% 7.85/8.04        | ~ (l1_struct_0 @ sk_A))),
% 7.85/8.04      inference('sup+', [status(thm)], ['107', '110'])).
% 7.85/8.04  thf('112', plain, ((l1_struct_0 @ sk_A)),
% 7.85/8.04      inference('sup-', [status(thm)], ['36', '37'])).
% 7.85/8.04  thf('113', plain,
% 7.85/8.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 7.85/8.04         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))),
% 7.85/8.04      inference('demod', [status(thm)], ['111', '112'])).
% 7.85/8.04  thf('114', plain,
% 7.85/8.04      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 7.85/8.04         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1))),
% 7.85/8.04      inference('sup+', [status(thm)], ['106', '113'])).
% 7.85/8.04  thf('115', plain,
% 7.85/8.04      (((u1_struct_0 @ sk_A)
% 7.85/8.04         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 7.85/8.04      inference('demod', [status(thm)], ['52', '55', '91', '94', '99', '114'])).
% 7.85/8.04  thf('116', plain,
% 7.85/8.04      ((((u1_struct_0 @ sk_A)
% 7.85/8.04          = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04             (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))
% 7.85/8.04        | ~ (l1_struct_0 @ sk_A))),
% 7.85/8.04      inference('sup+', [status(thm)], ['47', '115'])).
% 7.85/8.04  thf('117', plain, ((l1_struct_0 @ sk_A)),
% 7.85/8.04      inference('sup-', [status(thm)], ['36', '37'])).
% 7.85/8.04  thf('118', plain,
% 7.85/8.04      (((u1_struct_0 @ sk_A)
% 7.85/8.04         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 7.85/8.04      inference('demod', [status(thm)], ['116', '117'])).
% 7.85/8.04  thf('119', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.85/8.04      inference('demod', [status(thm)], ['102', '103'])).
% 7.85/8.04  thf('120', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.85/8.04      inference('demod', [status(thm)], ['102', '103'])).
% 7.85/8.04  thf('121', plain,
% 7.85/8.04      (![X45 : $i, X46 : $i, X47 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 7.85/8.04          | ((k3_subset_1 @ X46 @ (k7_subset_1 @ X46 @ X47 @ X45))
% 7.85/8.04              = (k4_subset_1 @ X46 @ (k3_subset_1 @ X46 @ X47) @ X45))
% 7.85/8.04          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46)))),
% 7.85/8.04      inference('cnf', [status(esa)], [t33_subset_1])).
% 7.85/8.04  thf('122', plain,
% 7.85/8.04      (![X0 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 7.85/8.04          | ((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04              (k7_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C_1))
% 7.85/8.04              = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04                 (k3_subset_1 @ (k2_struct_0 @ sk_A) @ X0) @ sk_C_1)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['120', '121'])).
% 7.85/8.04  thf('123', plain,
% 7.85/8.04      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04         (k7_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ sk_C_1))
% 7.85/8.04         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 7.85/8.04      inference('sup-', [status(thm)], ['119', '122'])).
% 7.85/8.04  thf('124', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 7.85/8.04      inference('demod', [status(thm)], ['102', '103'])).
% 7.85/8.04  thf('125', plain,
% 7.85/8.04      (![X42 : $i, X43 : $i, X44 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 7.85/8.04          | ((k7_subset_1 @ X43 @ X42 @ X44) = (k4_xboole_0 @ X42 @ X44)))),
% 7.85/8.04      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 7.85/8.04  thf('126', plain,
% 7.85/8.04      (![X0 : $i]:
% 7.85/8.04         ((k7_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 7.85/8.04           = (k4_xboole_0 @ sk_C_1 @ X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['124', '125'])).
% 7.85/8.04  thf('127', plain,
% 7.85/8.04      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['89', '90'])).
% 7.85/8.04  thf('128', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 7.85/8.04      inference('sup+', [status(thm)], ['92', '93'])).
% 7.85/8.04  thf('129', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 7.85/8.04      inference('sup+', [status(thm)], ['97', '98'])).
% 7.85/8.04  thf('130', plain,
% 7.85/8.04      (((k2_struct_0 @ sk_A)
% 7.85/8.04         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 7.85/8.04      inference('demod', [status(thm)], ['123', '126', '127', '128', '129'])).
% 7.85/8.04  thf('131', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.85/8.04      inference('sup+', [status(thm)], ['118', '130'])).
% 7.85/8.04  thf('132', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.85/8.04      inference('clc', [status(thm)], ['87', '88'])).
% 7.85/8.04  thf('133', plain,
% 7.85/8.04      (![X42 : $i, X43 : $i, X44 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 7.85/8.04          | ((k7_subset_1 @ X43 @ X42 @ X44) = (k4_xboole_0 @ X42 @ X44)))),
% 7.85/8.04      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 7.85/8.04  thf('134', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 7.85/8.04      inference('sup-', [status(thm)], ['132', '133'])).
% 7.85/8.04  thf('135', plain,
% 7.85/8.04      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['35', '38'])).
% 7.85/8.04  thf('136', plain,
% 7.85/8.04      (![X36 : $i, X37 : $i]:
% 7.85/8.04         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 7.85/8.04          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 7.85/8.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.85/8.04  thf('137', plain,
% 7.85/8.04      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['135', '136'])).
% 7.85/8.04  thf('138', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.85/8.04      inference('sup+', [status(thm)], ['118', '130'])).
% 7.85/8.04  thf('139', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 7.85/8.04      inference('sup-', [status(thm)], ['132', '133'])).
% 7.85/8.04  thf('140', plain,
% 7.85/8.04      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['135', '136'])).
% 7.85/8.04  thf('141', plain,
% 7.85/8.04      (((~ (v3_pre_topc @ sk_D @ sk_A)
% 7.85/8.04         | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))
% 7.85/8.04             = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)],
% 7.85/8.04                ['46', '131', '134', '137', '138', '139', '140'])).
% 7.85/8.04  thf('142', plain,
% 7.85/8.04      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))
% 7.85/8.04          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 7.85/8.04             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['32', '141'])).
% 7.85/8.04  thf('143', plain,
% 7.85/8.04      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['35', '38'])).
% 7.85/8.04  thf('144', plain,
% 7.85/8.04      (![X52 : $i]:
% 7.85/8.04         (((k2_struct_0 @ X52) = (u1_struct_0 @ X52)) | ~ (l1_struct_0 @ X52))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.85/8.04  thf(d1_tops_1, axiom,
% 7.85/8.04    (![A:$i]:
% 7.85/8.04     ( ( l1_pre_topc @ A ) =>
% 7.85/8.04       ( ![B:$i]:
% 7.85/8.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.85/8.04           ( ( k1_tops_1 @ A @ B ) =
% 7.85/8.04             ( k3_subset_1 @
% 7.85/8.04               ( u1_struct_0 @ A ) @ 
% 7.85/8.04               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 7.85/8.04  thf('145', plain,
% 7.85/8.04      (![X56 : $i, X57 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 7.85/8.04          | ((k1_tops_1 @ X57 @ X56)
% 7.85/8.04              = (k3_subset_1 @ (u1_struct_0 @ X57) @ 
% 7.85/8.04                 (k2_pre_topc @ X57 @ (k3_subset_1 @ (u1_struct_0 @ X57) @ X56))))
% 7.85/8.04          | ~ (l1_pre_topc @ X57))),
% 7.85/8.04      inference('cnf', [status(esa)], [d1_tops_1])).
% 7.85/8.04  thf('146', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 7.85/8.04          | ~ (l1_struct_0 @ X0)
% 7.85/8.04          | ~ (l1_pre_topc @ X0)
% 7.85/8.04          | ((k1_tops_1 @ X0 @ X1)
% 7.85/8.04              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 7.85/8.04                 (k2_pre_topc @ X0 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['144', '145'])).
% 7.85/8.04  thf('147', plain,
% 7.85/8.04      (((((k1_tops_1 @ sk_A @ sk_D)
% 7.85/8.04           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04              (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 7.85/8.04         | ~ (l1_pre_topc @ sk_A)
% 7.85/8.04         | ~ (l1_struct_0 @ sk_A)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['143', '146'])).
% 7.85/8.04  thf('148', plain,
% 7.85/8.04      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['135', '136'])).
% 7.85/8.04  thf('149', plain,
% 7.85/8.04      (![X52 : $i]:
% 7.85/8.04         (((k2_struct_0 @ X52) = (u1_struct_0 @ X52)) | ~ (l1_struct_0 @ X52))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.85/8.04  thf('150', plain,
% 7.85/8.04      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('split', [status(esa)], ['4'])).
% 7.85/8.04  thf('151', plain,
% 7.85/8.04      (![X36 : $i, X37 : $i]:
% 7.85/8.04         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 7.85/8.04          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 7.85/8.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.85/8.04  thf('152', plain,
% 7.85/8.04      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['150', '151'])).
% 7.85/8.04  thf('153', plain,
% 7.85/8.04      (((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04           = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D))
% 7.85/8.04         | ~ (l1_struct_0 @ sk_A)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup+', [status(thm)], ['149', '152'])).
% 7.85/8.04  thf('154', plain, ((l1_struct_0 @ sk_A)),
% 7.85/8.04      inference('sup-', [status(thm)], ['36', '37'])).
% 7.85/8.04  thf('155', plain,
% 7.85/8.04      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['153', '154'])).
% 7.85/8.04  thf('156', plain,
% 7.85/8.04      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup+', [status(thm)], ['148', '155'])).
% 7.85/8.04  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('158', plain, ((l1_struct_0 @ sk_A)),
% 7.85/8.04      inference('sup-', [status(thm)], ['36', '37'])).
% 7.85/8.04  thf('159', plain,
% 7.85/8.04      ((((k1_tops_1 @ sk_A @ sk_D)
% 7.85/8.04          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['147', '156', '157', '158'])).
% 7.85/8.04  thf('160', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 7.85/8.04      inference('sup+', [status(thm)], ['118', '130'])).
% 7.85/8.04  thf('161', plain,
% 7.85/8.04      ((((k1_tops_1 @ sk_A @ sk_D)
% 7.85/8.04          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['159', '160'])).
% 7.85/8.04  thf('162', plain,
% 7.85/8.04      ((((k1_tops_1 @ sk_A @ sk_D)
% 7.85/8.04          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04             (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))))
% 7.85/8.04         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 7.85/8.04             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup+', [status(thm)], ['142', '161'])).
% 7.85/8.04  thf('163', plain,
% 7.85/8.04      (![X52 : $i]:
% 7.85/8.04         (((k2_struct_0 @ X52) = (u1_struct_0 @ X52)) | ~ (l1_struct_0 @ X52))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 7.85/8.04  thf('164', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.85/8.04      inference('clc', [status(thm)], ['87', '88'])).
% 7.85/8.04  thf('165', plain,
% 7.85/8.04      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('split', [status(esa)], ['4'])).
% 7.85/8.04  thf('166', plain,
% 7.85/8.04      (![X45 : $i, X46 : $i, X47 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 7.85/8.04          | ((k3_subset_1 @ X46 @ (k7_subset_1 @ X46 @ X47 @ X45))
% 7.85/8.04              = (k4_subset_1 @ X46 @ (k3_subset_1 @ X46 @ X47) @ X45))
% 7.85/8.04          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46)))),
% 7.85/8.04      inference('cnf', [status(esa)], [t33_subset_1])).
% 7.85/8.04  thf('167', plain,
% 7.85/8.04      ((![X0 : $i]:
% 7.85/8.04          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04           | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04               (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D))
% 7.85/8.04               = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_D))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['165', '166'])).
% 7.85/8.04  thf('168', plain,
% 7.85/8.04      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_D))
% 7.85/8.04          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['164', '167'])).
% 7.85/8.04  thf('169', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 7.85/8.04      inference('sup-', [status(thm)], ['132', '133'])).
% 7.85/8.04  thf('170', plain,
% 7.85/8.04      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['150', '151'])).
% 7.85/8.04  thf('171', plain,
% 7.85/8.04      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup+', [status(thm)], ['148', '155'])).
% 7.85/8.04  thf('172', plain,
% 7.85/8.04      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 7.85/8.04          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['170', '171'])).
% 7.85/8.04  thf('173', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 7.85/8.04      inference('sup+', [status(thm)], ['92', '93'])).
% 7.85/8.04  thf('174', plain,
% 7.85/8.04      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('split', [status(esa)], ['4'])).
% 7.85/8.04  thf('175', plain,
% 7.85/8.04      (![X48 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 7.85/8.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.85/8.04  thf(redefinition_k4_subset_1, axiom,
% 7.85/8.04    (![A:$i,B:$i,C:$i]:
% 7.85/8.04     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 7.85/8.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.85/8.04       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 7.85/8.04  thf('176', plain,
% 7.85/8.04      (![X39 : $i, X40 : $i, X41 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 7.85/8.04          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 7.85/8.04          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 7.85/8.04      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 7.85/8.04  thf('177', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 7.85/8.04            = (k2_xboole_0 @ k1_xboole_0 @ X1))
% 7.85/8.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['175', '176'])).
% 7.85/8.04  thf('178', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 7.85/8.04      inference('cnf', [status(esa)], [t65_xboole_1])).
% 7.85/8.04  thf('179', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 7.85/8.04      inference('cnf', [status(esa)], [t1_boole])).
% 7.85/8.04  thf('180', plain,
% 7.85/8.04      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 7.85/8.04         (((X19) = (X18))
% 7.85/8.04          | ~ (r1_xboole_0 @ X19 @ X20)
% 7.85/8.04          | ((k2_xboole_0 @ X20 @ X18) != (k2_xboole_0 @ X19 @ X21))
% 7.85/8.04          | ~ (r1_xboole_0 @ X21 @ X18))),
% 7.85/8.04      inference('cnf', [status(esa)], [t72_xboole_1])).
% 7.85/8.04  thf('181', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.85/8.04         (((k2_xboole_0 @ X2 @ X1) != (X0))
% 7.85/8.04          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 7.85/8.04          | ~ (r1_xboole_0 @ X0 @ X2)
% 7.85/8.04          | ((X0) = (X1)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['179', '180'])).
% 7.85/8.04  thf('182', plain,
% 7.85/8.04      (![X1 : $i, X2 : $i]:
% 7.85/8.04         (((k2_xboole_0 @ X2 @ X1) = (X1))
% 7.85/8.04          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2)
% 7.85/8.04          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 7.85/8.04      inference('simplify', [status(thm)], ['181'])).
% 7.85/8.04  thf('183', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 7.85/8.04      inference('cnf', [status(esa)], [t3_boole])).
% 7.85/8.04  thf('184', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['60', '61'])).
% 7.85/8.04  thf('185', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 7.85/8.04      inference('sup+', [status(thm)], ['183', '184'])).
% 7.85/8.04  thf('186', plain,
% 7.85/8.04      (![X1 : $i, X2 : $i]:
% 7.85/8.04         (((k2_xboole_0 @ X2 @ X1) = (X1))
% 7.85/8.04          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2))),
% 7.85/8.04      inference('demod', [status(thm)], ['182', '185'])).
% 7.85/8.04  thf('187', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 7.85/8.04      inference('sup-', [status(thm)], ['178', '186'])).
% 7.85/8.04  thf('188', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i]:
% 7.85/8.04         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1) = (X1))
% 7.85/8.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 7.85/8.04      inference('demod', [status(thm)], ['177', '187'])).
% 7.85/8.04  thf('189', plain,
% 7.85/8.04      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ sk_D) = (sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['174', '188'])).
% 7.85/8.04  thf('190', plain,
% 7.85/8.04      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.85/8.04          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['168', '169', '172', '173', '189'])).
% 7.85/8.04  thf('191', plain,
% 7.85/8.04      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04           (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)) = (sk_D))
% 7.85/8.04         | ~ (l1_struct_0 @ sk_A)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup+', [status(thm)], ['163', '190'])).
% 7.85/8.04  thf('192', plain, ((l1_struct_0 @ sk_A)),
% 7.85/8.04      inference('sup-', [status(thm)], ['36', '37'])).
% 7.85/8.04  thf('193', plain,
% 7.85/8.04      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 7.85/8.04          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['191', '192'])).
% 7.85/8.04  thf('194', plain,
% 7.85/8.04      ((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)))
% 7.85/8.04         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 7.85/8.04             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup+', [status(thm)], ['162', '193'])).
% 7.85/8.04  thf('195', plain,
% 7.85/8.04      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 7.85/8.04      inference('split', [status(esa)], ['2'])).
% 7.85/8.04  thf('196', plain,
% 7.85/8.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('197', plain,
% 7.85/8.04      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('split', [status(esa)], ['4'])).
% 7.85/8.04  thf(t48_tops_1, axiom,
% 7.85/8.04    (![A:$i]:
% 7.85/8.04     ( ( l1_pre_topc @ A ) =>
% 7.85/8.04       ( ![B:$i]:
% 7.85/8.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.85/8.04           ( ![C:$i]:
% 7.85/8.04             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.85/8.04               ( ( r1_tarski @ B @ C ) =>
% 7.85/8.04                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 7.85/8.04  thf('198', plain,
% 7.85/8.04      (![X64 : $i, X65 : $i, X66 : $i]:
% 7.85/8.04         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 7.85/8.04          | ~ (r1_tarski @ X64 @ X66)
% 7.85/8.04          | (r1_tarski @ (k1_tops_1 @ X65 @ X64) @ (k1_tops_1 @ X65 @ X66))
% 7.85/8.04          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 7.85/8.04          | ~ (l1_pre_topc @ X65))),
% 7.85/8.04      inference('cnf', [status(esa)], [t48_tops_1])).
% 7.85/8.04  thf('199', plain,
% 7.85/8.04      ((![X0 : $i]:
% 7.85/8.04          (~ (l1_pre_topc @ sk_A)
% 7.85/8.04           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 7.85/8.04           | ~ (r1_tarski @ sk_D @ X0)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['197', '198'])).
% 7.85/8.04  thf('200', plain, ((l1_pre_topc @ sk_A)),
% 7.85/8.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.85/8.04  thf('201', plain,
% 7.85/8.04      ((![X0 : $i]:
% 7.85/8.04          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.85/8.04           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 7.85/8.04           | ~ (r1_tarski @ sk_D @ X0)))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('demod', [status(thm)], ['199', '200'])).
% 7.85/8.04  thf('202', plain,
% 7.85/8.04      (((~ (r1_tarski @ sk_D @ sk_C_1)
% 7.85/8.04         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 7.85/8.04         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['196', '201'])).
% 7.85/8.04  thf('203', plain,
% 7.85/8.04      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 7.85/8.04         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 7.85/8.04             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['195', '202'])).
% 7.85/8.04  thf('204', plain,
% 7.85/8.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.85/8.04         (~ (r2_hidden @ X0 @ X1)
% 7.85/8.04          | (r2_hidden @ X0 @ X2)
% 7.85/8.04          | ~ (r1_tarski @ X1 @ X2))),
% 7.85/8.04      inference('cnf', [status(esa)], [d3_tarski])).
% 7.85/8.04  thf('205', plain,
% 7.85/8.04      ((![X0 : $i]:
% 7.85/8.04          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 7.85/8.04           | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))))
% 7.85/8.04         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 7.85/8.04             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['203', '204'])).
% 7.85/8.04  thf('206', plain,
% 7.85/8.04      ((![X0 : $i]:
% 7.85/8.04          (~ (r2_hidden @ X0 @ sk_D)
% 7.85/8.04           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 7.85/8.04         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 7.85/8.04             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 7.85/8.04             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['194', '205'])).
% 7.85/8.04  thf('207', plain,
% 7.85/8.04      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 7.85/8.04         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 7.85/8.04             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 7.85/8.04             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 7.85/8.04             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 7.85/8.04      inference('sup-', [status(thm)], ['31', '206'])).
% 7.85/8.04  thf('208', plain,
% 7.85/8.04      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 7.85/8.04         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 7.85/8.04      inference('split', [status(esa)], ['6'])).
% 7.85/8.04  thf('209', plain,
% 7.85/8.04      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 7.85/8.04       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 7.85/8.04       ~ ((r1_tarski @ sk_D @ sk_C_1)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 7.85/8.04       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 7.85/8.04      inference('sup-', [status(thm)], ['207', '208'])).
% 7.85/8.04  thf('210', plain, ($false),
% 7.85/8.04      inference('sat_resolution*', [status(thm)],
% 7.85/8.04                ['1', '3', '5', '7', '28', '30', '209'])).
% 7.85/8.04  
% 7.85/8.04  % SZS output end Refutation
% 7.85/8.04  
% 7.85/8.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
