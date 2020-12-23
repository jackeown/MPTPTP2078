%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xHJqmo4raf

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:39 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 593 expanded)
%              Number of leaves         :   51 ( 198 expanded)
%              Depth                    :   19
%              Number of atoms          : 1781 (6675 expanded)
%              Number of equality atoms :  141 ( 478 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( v4_pre_topc @ X60 @ X61 )
      | ( ( k2_pre_topc @ X61 @ X60 )
        = X60 )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( l1_pre_topc @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k4_subset_1 @ X46 @ X45 @ X47 )
        = ( k2_xboole_0 @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( ( k2_pre_topc @ X67 @ X66 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X67 ) @ X66 @ ( k2_tops_1 @ X67 @ X66 ) ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k6_subset_1 @ X48 @ X49 )
      = ( k4_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ X20 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('29',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k6_subset_1 @ X48 @ X49 )
      = ( k4_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X26 @ X27 ) @ X28 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X55: $i,X57: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r1_tarski @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('36',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X44 @ ( k3_subset_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('37',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k4_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k6_subset_1 @ X48 @ X49 )
      = ( k4_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k6_subset_1 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X69 ) ) )
      | ( ( k1_tops_1 @ X69 @ X68 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X69 ) @ X68 @ ( k2_tops_1 @ X69 @ X68 ) ) )
      | ~ ( l1_pre_topc @ X69 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ( ( k7_subset_1 @ X51 @ X50 @ X52 )
        = ( k4_xboole_0 @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('49',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k6_subset_1 @ X48 @ X49 )
      = ( k4_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('50',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ( ( k7_subset_1 @ X51 @ X50 @ X52 )
        = ( k6_subset_1 @ X50 @ X52 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','51'])).

thf('53',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','52'])).

thf('54',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','53'])).

thf('55',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','51'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X41: $i,X42: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('57',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k6_subset_1 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','51'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('69',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('70',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k6_subset_1 @ X48 @ X49 )
      = ( k4_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('72',plain,(
    ! [X22: $i] :
      ( ( k6_subset_1 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('73',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('74',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k6_subset_1 @ X48 @ X49 )
      = ( k4_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('76',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k6_subset_1 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('80',plain,(
    ! [X19: $i] :
      ( ( k3_xboole_0 @ X19 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ X20 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('86',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('87',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('88',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('92',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('93',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k6_subset_1 @ X48 @ X49 )
      = ( k4_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('94',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','95'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k6_subset_1 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('100',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','100'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('102',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X34 @ X33 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('103',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X53 @ X54 ) )
      = ( k3_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X53 @ X54 ) )
      = ( k3_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('107',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X29 @ X30 ) @ ( k4_xboole_0 @ X29 @ X30 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('108',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k6_subset_1 @ X48 @ X49 )
      = ( k4_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('109',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X34 @ X33 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('110',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) )
      = X29 ) ),
    inference(demod,[status(thm)],['107','108','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['106','114'])).

thf('116',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['101','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('118',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','119'])).

thf('121',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','51'])).

thf('122',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) )
      = X29 ) ),
    inference(demod,[status(thm)],['107','108','113'])).

thf('123',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('126',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('130',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('132',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('134',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( v2_pre_topc @ X61 )
      | ( ( k2_pre_topc @ X61 @ X60 )
       != X60 )
      | ( v4_pre_topc @ X60 @ X61 )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','140'])).

thf('142',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('144',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','67','68','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xHJqmo4raf
% 0.13/0.37  % Computer   : n007.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:31:06 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.72/1.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.93  % Solved by: fo/fo7.sh
% 1.72/1.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.93  % done 2343 iterations in 1.446s
% 1.72/1.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.93  % SZS output start Refutation
% 1.72/1.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.93  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.72/1.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.72/1.93  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.72/1.93  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.72/1.93  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.72/1.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.72/1.93  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.72/1.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.93  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.72/1.93  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.72/1.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.72/1.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.93  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.72/1.93  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.72/1.93  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.72/1.93  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.93  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.72/1.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.72/1.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.72/1.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.72/1.93  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.72/1.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.72/1.93  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.72/1.93  thf(t77_tops_1, conjecture,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.72/1.93       ( ![B:$i]:
% 1.72/1.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.93           ( ( v4_pre_topc @ B @ A ) <=>
% 1.72/1.93             ( ( k2_tops_1 @ A @ B ) =
% 1.72/1.93               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.72/1.93  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.93    (~( ![A:$i]:
% 1.72/1.93        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.72/1.93          ( ![B:$i]:
% 1.72/1.93            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.93              ( ( v4_pre_topc @ B @ A ) <=>
% 1.72/1.93                ( ( k2_tops_1 @ A @ B ) =
% 1.72/1.93                  ( k7_subset_1 @
% 1.72/1.93                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.72/1.93    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.72/1.93  thf('0', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93              (k1_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('1', plain,
% 1.72/1.93      (~
% 1.72/1.93       (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.72/1.93       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('split', [status(esa)], ['0'])).
% 1.72/1.93  thf('2', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93             (k1_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('3', plain,
% 1.72/1.93      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('split', [status(esa)], ['2'])).
% 1.72/1.93  thf('4', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(t52_pre_topc, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( l1_pre_topc @ A ) =>
% 1.72/1.93       ( ![B:$i]:
% 1.72/1.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.93           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.72/1.93             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.72/1.93               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.72/1.93  thf('5', plain,
% 1.72/1.93      (![X60 : $i, X61 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 1.72/1.93          | ~ (v4_pre_topc @ X60 @ X61)
% 1.72/1.93          | ((k2_pre_topc @ X61 @ X60) = (X60))
% 1.72/1.93          | ~ (l1_pre_topc @ X61))),
% 1.72/1.93      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.72/1.93  thf('6', plain,
% 1.72/1.93      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.93        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.72/1.93        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('sup-', [status(thm)], ['4', '5'])).
% 1.72/1.93  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('8', plain,
% 1.72/1.93      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('demod', [status(thm)], ['6', '7'])).
% 1.72/1.93  thf('9', plain,
% 1.72/1.93      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.72/1.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['3', '8'])).
% 1.72/1.93  thf('10', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(dt_k2_tops_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( ( l1_pre_topc @ A ) & 
% 1.72/1.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.72/1.93       ( m1_subset_1 @
% 1.72/1.93         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.72/1.93  thf('11', plain,
% 1.72/1.93      (![X62 : $i, X63 : $i]:
% 1.72/1.93         (~ (l1_pre_topc @ X62)
% 1.72/1.93          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 1.72/1.93          | (m1_subset_1 @ (k2_tops_1 @ X62 @ X63) @ 
% 1.72/1.93             (k1_zfmisc_1 @ (u1_struct_0 @ X62))))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.72/1.93  thf('12', plain,
% 1.72/1.93      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.72/1.93         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.72/1.93        | ~ (l1_pre_topc @ sk_A))),
% 1.72/1.93      inference('sup-', [status(thm)], ['10', '11'])).
% 1.72/1.93  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('14', plain,
% 1.72/1.93      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.72/1.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.93      inference('demod', [status(thm)], ['12', '13'])).
% 1.72/1.93  thf('15', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(redefinition_k4_subset_1, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.72/1.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.72/1.93       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.72/1.93  thf('16', plain,
% 1.72/1.93      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 1.72/1.93          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46))
% 1.72/1.93          | ((k4_subset_1 @ X46 @ X45 @ X47) = (k2_xboole_0 @ X45 @ X47)))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.72/1.93  thf('17', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.72/1.93            = (k2_xboole_0 @ sk_B @ X0))
% 1.72/1.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['15', '16'])).
% 1.72/1.93  thf('18', plain,
% 1.72/1.93      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.72/1.93         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['14', '17'])).
% 1.72/1.93  thf('19', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(t65_tops_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( l1_pre_topc @ A ) =>
% 1.72/1.93       ( ![B:$i]:
% 1.72/1.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.93           ( ( k2_pre_topc @ A @ B ) =
% 1.72/1.93             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.72/1.93  thf('20', plain,
% 1.72/1.93      (![X66 : $i, X67 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 1.72/1.93          | ((k2_pre_topc @ X67 @ X66)
% 1.72/1.93              = (k4_subset_1 @ (u1_struct_0 @ X67) @ X66 @ 
% 1.72/1.93                 (k2_tops_1 @ X67 @ X66)))
% 1.72/1.93          | ~ (l1_pre_topc @ X67))),
% 1.72/1.93      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.72/1.93  thf('21', plain,
% 1.72/1.93      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.93        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.72/1.93            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['19', '20'])).
% 1.72/1.93  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('23', plain,
% 1.72/1.93      (((k2_pre_topc @ sk_A @ sk_B)
% 1.72/1.93         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('demod', [status(thm)], ['21', '22'])).
% 1.72/1.93  thf('24', plain,
% 1.72/1.93      (((k2_pre_topc @ sk_A @ sk_B)
% 1.72/1.93         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('sup+', [status(thm)], ['18', '23'])).
% 1.72/1.93  thf(t36_xboole_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.72/1.93  thf('25', plain,
% 1.72/1.93      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 1.72/1.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.72/1.93  thf(redefinition_k6_subset_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.72/1.93  thf('26', plain,
% 1.72/1.93      (![X48 : $i, X49 : $i]:
% 1.72/1.93         ((k6_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.72/1.93  thf('27', plain,
% 1.72/1.93      (![X20 : $i, X21 : $i]: (r1_tarski @ (k6_subset_1 @ X20 @ X21) @ X20)),
% 1.72/1.93      inference('demod', [status(thm)], ['25', '26'])).
% 1.72/1.93  thf(t44_xboole_1, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.72/1.93       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.72/1.93  thf('28', plain,
% 1.72/1.93      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.72/1.93         ((r1_tarski @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 1.72/1.93          | ~ (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X28))),
% 1.72/1.93      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.72/1.93  thf('29', plain,
% 1.72/1.93      (![X48 : $i, X49 : $i]:
% 1.72/1.93         ((k6_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.72/1.93  thf('30', plain,
% 1.72/1.93      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.72/1.93         ((r1_tarski @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 1.72/1.93          | ~ (r1_tarski @ (k6_subset_1 @ X26 @ X27) @ X28))),
% 1.72/1.93      inference('demod', [status(thm)], ['28', '29'])).
% 1.72/1.93  thf('31', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.72/1.93      inference('sup-', [status(thm)], ['27', '30'])).
% 1.72/1.93  thf('32', plain,
% 1.72/1.93      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))),
% 1.72/1.93      inference('sup+', [status(thm)], ['24', '31'])).
% 1.72/1.93  thf('33', plain,
% 1.72/1.93      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.72/1.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('sup+', [status(thm)], ['9', '32'])).
% 1.72/1.93  thf(t3_subset, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.72/1.93  thf('34', plain,
% 1.72/1.93      (![X55 : $i, X57 : $i]:
% 1.72/1.93         ((m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X57)) | ~ (r1_tarski @ X55 @ X57))),
% 1.72/1.93      inference('cnf', [status(esa)], [t3_subset])).
% 1.72/1.93  thf('35', plain,
% 1.72/1.93      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.72/1.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['33', '34'])).
% 1.72/1.93  thf(involutiveness_k3_subset_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.93       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.72/1.93  thf('36', plain,
% 1.72/1.93      (![X43 : $i, X44 : $i]:
% 1.72/1.93         (((k3_subset_1 @ X44 @ (k3_subset_1 @ X44 @ X43)) = (X43))
% 1.72/1.93          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 1.72/1.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.72/1.93  thf('37', plain,
% 1.72/1.93      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['35', '36'])).
% 1.72/1.93  thf('38', plain,
% 1.72/1.93      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.72/1.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['33', '34'])).
% 1.72/1.93  thf(d5_subset_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.93       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.72/1.93  thf('39', plain,
% 1.72/1.93      (![X37 : $i, X38 : $i]:
% 1.72/1.93         (((k3_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))
% 1.72/1.93          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 1.72/1.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.72/1.93  thf('40', plain,
% 1.72/1.93      (![X48 : $i, X49 : $i]:
% 1.72/1.93         ((k6_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.72/1.93  thf('41', plain,
% 1.72/1.93      (![X37 : $i, X38 : $i]:
% 1.72/1.93         (((k3_subset_1 @ X37 @ X38) = (k6_subset_1 @ X37 @ X38))
% 1.72/1.93          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 1.72/1.93      inference('demod', [status(thm)], ['39', '40'])).
% 1.72/1.93  thf('42', plain,
% 1.72/1.93      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.72/1.93          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.72/1.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['38', '41'])).
% 1.72/1.93  thf('43', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(t74_tops_1, axiom,
% 1.72/1.93    (![A:$i]:
% 1.72/1.93     ( ( l1_pre_topc @ A ) =>
% 1.72/1.93       ( ![B:$i]:
% 1.72/1.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.93           ( ( k1_tops_1 @ A @ B ) =
% 1.72/1.93             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.72/1.93  thf('44', plain,
% 1.72/1.93      (![X68 : $i, X69 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X69)))
% 1.72/1.93          | ((k1_tops_1 @ X69 @ X68)
% 1.72/1.93              = (k7_subset_1 @ (u1_struct_0 @ X69) @ X68 @ 
% 1.72/1.93                 (k2_tops_1 @ X69 @ X68)))
% 1.72/1.93          | ~ (l1_pre_topc @ X69))),
% 1.72/1.93      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.72/1.93  thf('45', plain,
% 1.72/1.93      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.93        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.93            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['43', '44'])).
% 1.72/1.93  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('47', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf(redefinition_k7_subset_1, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.93       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.72/1.93  thf('48', plain,
% 1.72/1.93      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 1.72/1.93          | ((k7_subset_1 @ X51 @ X50 @ X52) = (k4_xboole_0 @ X50 @ X52)))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.72/1.93  thf('49', plain,
% 1.72/1.93      (![X48 : $i, X49 : $i]:
% 1.72/1.93         ((k6_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.72/1.93  thf('50', plain,
% 1.72/1.93      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 1.72/1.93          | ((k7_subset_1 @ X51 @ X50 @ X52) = (k6_subset_1 @ X50 @ X52)))),
% 1.72/1.93      inference('demod', [status(thm)], ['48', '49'])).
% 1.72/1.93  thf('51', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.72/1.93           = (k6_subset_1 @ sk_B @ X0))),
% 1.72/1.93      inference('sup-', [status(thm)], ['47', '50'])).
% 1.72/1.93  thf('52', plain,
% 1.72/1.93      (((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.93         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('demod', [status(thm)], ['45', '46', '51'])).
% 1.72/1.93  thf('53', plain,
% 1.72/1.93      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.72/1.93          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('demod', [status(thm)], ['42', '52'])).
% 1.72/1.93  thf('54', plain,
% 1.72/1.93      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.72/1.93          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('demod', [status(thm)], ['37', '53'])).
% 1.72/1.93  thf('55', plain,
% 1.72/1.93      (((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.93         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('demod', [status(thm)], ['45', '46', '51'])).
% 1.72/1.93  thf(dt_k6_subset_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.72/1.93  thf('56', plain,
% 1.72/1.93      (![X41 : $i, X42 : $i]:
% 1.72/1.93         (m1_subset_1 @ (k6_subset_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41))),
% 1.72/1.93      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.72/1.93  thf('57', plain,
% 1.72/1.93      (![X37 : $i, X38 : $i]:
% 1.72/1.93         (((k3_subset_1 @ X37 @ X38) = (k6_subset_1 @ X37 @ X38))
% 1.72/1.93          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 1.72/1.93      inference('demod', [status(thm)], ['39', '40'])).
% 1.72/1.93  thf('58', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.72/1.93           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['56', '57'])).
% 1.72/1.93  thf('59', plain,
% 1.72/1.93      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.72/1.93         = (k6_subset_1 @ sk_B @ 
% 1.72/1.93            (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['55', '58'])).
% 1.72/1.93  thf('60', plain,
% 1.72/1.93      (((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.93         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('demod', [status(thm)], ['45', '46', '51'])).
% 1.72/1.93  thf('61', plain,
% 1.72/1.93      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.72/1.93         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('demod', [status(thm)], ['59', '60'])).
% 1.72/1.93  thf('62', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.72/1.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('sup+', [status(thm)], ['54', '61'])).
% 1.72/1.93  thf('63', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.72/1.93           = (k6_subset_1 @ sk_B @ X0))),
% 1.72/1.93      inference('sup-', [status(thm)], ['47', '50'])).
% 1.72/1.93  thf('64', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93              (k1_tops_1 @ sk_A @ sk_B))))
% 1.72/1.93         <= (~
% 1.72/1.93             (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('split', [status(esa)], ['0'])).
% 1.72/1.93  thf('65', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.72/1.93         <= (~
% 1.72/1.93             (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['63', '64'])).
% 1.72/1.93  thf('66', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93         <= (~
% 1.72/1.93             (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.72/1.93             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['62', '65'])).
% 1.72/1.93  thf('67', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.72/1.93       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('simplify', [status(thm)], ['66'])).
% 1.72/1.93  thf('68', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.72/1.93       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('split', [status(esa)], ['2'])).
% 1.72/1.93  thf(d4_xboole_0, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.72/1.93       ( ![D:$i]:
% 1.72/1.93         ( ( r2_hidden @ D @ C ) <=>
% 1.72/1.93           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.72/1.93  thf('69', plain,
% 1.72/1.93      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.72/1.93         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.72/1.93          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.72/1.93          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.72/1.93      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.72/1.93  thf(t3_boole, axiom,
% 1.72/1.93    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.72/1.93  thf('70', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.72/1.93      inference('cnf', [status(esa)], [t3_boole])).
% 1.72/1.93  thf('71', plain,
% 1.72/1.93      (![X48 : $i, X49 : $i]:
% 1.72/1.93         ((k6_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.72/1.93  thf('72', plain, (![X22 : $i]: ((k6_subset_1 @ X22 @ k1_xboole_0) = (X22))),
% 1.72/1.93      inference('demod', [status(thm)], ['70', '71'])).
% 1.72/1.93  thf(d5_xboole_0, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.72/1.93       ( ![D:$i]:
% 1.72/1.93         ( ( r2_hidden @ D @ C ) <=>
% 1.72/1.93           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.72/1.93  thf('73', plain,
% 1.72/1.93      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.72/1.93         (~ (r2_hidden @ X14 @ X13)
% 1.72/1.93          | ~ (r2_hidden @ X14 @ X12)
% 1.72/1.93          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 1.72/1.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.72/1.93  thf('74', plain,
% 1.72/1.93      (![X11 : $i, X12 : $i, X14 : $i]:
% 1.72/1.93         (~ (r2_hidden @ X14 @ X12)
% 1.72/1.93          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 1.72/1.93      inference('simplify', [status(thm)], ['73'])).
% 1.72/1.93  thf('75', plain,
% 1.72/1.93      (![X48 : $i, X49 : $i]:
% 1.72/1.93         ((k6_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.72/1.93  thf('76', plain,
% 1.72/1.93      (![X11 : $i, X12 : $i, X14 : $i]:
% 1.72/1.93         (~ (r2_hidden @ X14 @ X12)
% 1.72/1.93          | ~ (r2_hidden @ X14 @ (k6_subset_1 @ X11 @ X12)))),
% 1.72/1.93      inference('demod', [status(thm)], ['74', '75'])).
% 1.72/1.93  thf('77', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.72/1.93      inference('sup-', [status(thm)], ['72', '76'])).
% 1.72/1.93  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.72/1.93      inference('condensation', [status(thm)], ['77'])).
% 1.72/1.93  thf('79', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 1.72/1.93          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.72/1.93      inference('sup-', [status(thm)], ['69', '78'])).
% 1.72/1.93  thf(t2_boole, axiom,
% 1.72/1.93    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.72/1.93  thf('80', plain,
% 1.72/1.93      (![X19 : $i]: ((k3_xboole_0 @ X19 @ k1_xboole_0) = (k1_xboole_0))),
% 1.72/1.93      inference('cnf', [status(esa)], [t2_boole])).
% 1.72/1.93  thf('81', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 1.72/1.93          | ((X1) = (k1_xboole_0)))),
% 1.72/1.93      inference('demod', [status(thm)], ['79', '80'])).
% 1.72/1.93  thf('82', plain,
% 1.72/1.93      (![X0 : $i]:
% 1.72/1.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.72/1.93           = (k6_subset_1 @ sk_B @ X0))),
% 1.72/1.93      inference('sup-', [status(thm)], ['47', '50'])).
% 1.72/1.93  thf('83', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93             (k1_tops_1 @ sk_A @ sk_B))))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('split', [status(esa)], ['2'])).
% 1.72/1.93  thf('84', plain,
% 1.72/1.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['82', '83'])).
% 1.72/1.93  thf('85', plain,
% 1.72/1.93      (![X20 : $i, X21 : $i]: (r1_tarski @ (k6_subset_1 @ X20 @ X21) @ X20)),
% 1.72/1.93      inference('demod', [status(thm)], ['25', '26'])).
% 1.72/1.93  thf('86', plain,
% 1.72/1.93      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['84', '85'])).
% 1.72/1.93  thf(t1_boole, axiom,
% 1.72/1.93    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.72/1.93  thf('87', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.72/1.93      inference('cnf', [status(esa)], [t1_boole])).
% 1.72/1.93  thf(t6_xboole_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.72/1.93  thf('88', plain,
% 1.72/1.93      (![X31 : $i, X32 : $i]:
% 1.72/1.93         ((k2_xboole_0 @ X31 @ (k2_xboole_0 @ X31 @ X32))
% 1.72/1.93           = (k2_xboole_0 @ X31 @ X32))),
% 1.72/1.93      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.72/1.93  thf('89', plain,
% 1.72/1.93      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.72/1.93      inference('sup+', [status(thm)], ['87', '88'])).
% 1.72/1.93  thf('90', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.72/1.93      inference('cnf', [status(esa)], [t1_boole])).
% 1.72/1.93  thf('91', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.72/1.93      inference('demod', [status(thm)], ['89', '90'])).
% 1.72/1.93  thf(t43_xboole_1, axiom,
% 1.72/1.93    (![A:$i,B:$i,C:$i]:
% 1.72/1.93     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.72/1.93       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.72/1.93  thf('92', plain,
% 1.72/1.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.72/1.93         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 1.72/1.93          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 1.72/1.93      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.72/1.93  thf('93', plain,
% 1.72/1.93      (![X48 : $i, X49 : $i]:
% 1.72/1.93         ((k6_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.72/1.93  thf('94', plain,
% 1.72/1.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.72/1.93         ((r1_tarski @ (k6_subset_1 @ X23 @ X24) @ X25)
% 1.72/1.93          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 1.72/1.93      inference('demod', [status(thm)], ['92', '93'])).
% 1.72/1.93  thf('95', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         (~ (r1_tarski @ X1 @ X0) | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ X0))),
% 1.72/1.93      inference('sup-', [status(thm)], ['91', '94'])).
% 1.72/1.93  thf('96', plain,
% 1.72/1.93      (((r1_tarski @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ sk_B))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['86', '95'])).
% 1.72/1.93  thf(d3_tarski, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( r1_tarski @ A @ B ) <=>
% 1.72/1.93       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.72/1.93  thf('97', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.93         (~ (r2_hidden @ X0 @ X1)
% 1.72/1.93          | (r2_hidden @ X0 @ X2)
% 1.72/1.93          | ~ (r1_tarski @ X1 @ X2))),
% 1.72/1.93      inference('cnf', [status(esa)], [d3_tarski])).
% 1.72/1.93  thf('98', plain,
% 1.72/1.93      ((![X0 : $i]:
% 1.72/1.93          ((r2_hidden @ X0 @ sk_B)
% 1.72/1.93           | ~ (r2_hidden @ X0 @ 
% 1.72/1.93                (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['96', '97'])).
% 1.72/1.93  thf('99', plain,
% 1.72/1.93      (![X11 : $i, X12 : $i, X14 : $i]:
% 1.72/1.93         (~ (r2_hidden @ X14 @ X12)
% 1.72/1.93          | ~ (r2_hidden @ X14 @ (k6_subset_1 @ X11 @ X12)))),
% 1.72/1.93      inference('demod', [status(thm)], ['74', '75'])).
% 1.72/1.93  thf('100', plain,
% 1.72/1.93      ((![X0 : $i]:
% 1.72/1.93          ~ (r2_hidden @ X0 @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('clc', [status(thm)], ['98', '99'])).
% 1.72/1.93  thf('101', plain,
% 1.72/1.93      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['81', '100'])).
% 1.72/1.93  thf(commutativity_k2_tarski, axiom,
% 1.72/1.93    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.72/1.93  thf('102', plain,
% 1.72/1.93      (![X33 : $i, X34 : $i]:
% 1.72/1.93         ((k2_tarski @ X34 @ X33) = (k2_tarski @ X33 @ X34))),
% 1.72/1.93      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.72/1.93  thf(t12_setfam_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.72/1.93  thf('103', plain,
% 1.72/1.93      (![X53 : $i, X54 : $i]:
% 1.72/1.93         ((k1_setfam_1 @ (k2_tarski @ X53 @ X54)) = (k3_xboole_0 @ X53 @ X54))),
% 1.72/1.93      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.72/1.93  thf('104', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.72/1.93      inference('sup+', [status(thm)], ['102', '103'])).
% 1.72/1.93  thf('105', plain,
% 1.72/1.93      (![X53 : $i, X54 : $i]:
% 1.72/1.93         ((k1_setfam_1 @ (k2_tarski @ X53 @ X54)) = (k3_xboole_0 @ X53 @ X54))),
% 1.72/1.93      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.72/1.93  thf('106', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.72/1.93      inference('sup+', [status(thm)], ['104', '105'])).
% 1.72/1.93  thf(t51_xboole_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.72/1.93       ( A ) ))).
% 1.72/1.93  thf('107', plain,
% 1.72/1.93      (![X29 : $i, X30 : $i]:
% 1.72/1.93         ((k2_xboole_0 @ (k3_xboole_0 @ X29 @ X30) @ (k4_xboole_0 @ X29 @ X30))
% 1.72/1.93           = (X29))),
% 1.72/1.93      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.72/1.93  thf('108', plain,
% 1.72/1.93      (![X48 : $i, X49 : $i]:
% 1.72/1.93         ((k6_subset_1 @ X48 @ X49) = (k4_xboole_0 @ X48 @ X49))),
% 1.72/1.93      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.72/1.93  thf('109', plain,
% 1.72/1.93      (![X33 : $i, X34 : $i]:
% 1.72/1.93         ((k2_tarski @ X34 @ X33) = (k2_tarski @ X33 @ X34))),
% 1.72/1.93      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.72/1.93  thf(l51_zfmisc_1, axiom,
% 1.72/1.93    (![A:$i,B:$i]:
% 1.72/1.93     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.72/1.93  thf('110', plain,
% 1.72/1.93      (![X35 : $i, X36 : $i]:
% 1.72/1.93         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 1.72/1.93      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.72/1.93  thf('111', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.72/1.93      inference('sup+', [status(thm)], ['109', '110'])).
% 1.72/1.93  thf('112', plain,
% 1.72/1.93      (![X35 : $i, X36 : $i]:
% 1.72/1.93         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 1.72/1.93      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.72/1.93  thf('113', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.72/1.93      inference('sup+', [status(thm)], ['111', '112'])).
% 1.72/1.93  thf('114', plain,
% 1.72/1.93      (![X29 : $i, X30 : $i]:
% 1.72/1.93         ((k2_xboole_0 @ (k6_subset_1 @ X29 @ X30) @ (k3_xboole_0 @ X29 @ X30))
% 1.72/1.93           = (X29))),
% 1.72/1.93      inference('demod', [status(thm)], ['107', '108', '113'])).
% 1.72/1.93  thf('115', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 1.72/1.93           = (X0))),
% 1.72/1.93      inference('sup+', [status(thm)], ['106', '114'])).
% 1.72/1.93  thf('116', plain,
% 1.72/1.93      ((((k2_xboole_0 @ k1_xboole_0 @ 
% 1.72/1.93          (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['101', '115'])).
% 1.72/1.93  thf('117', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.72/1.93      inference('sup+', [status(thm)], ['111', '112'])).
% 1.72/1.93  thf('118', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.72/1.93      inference('cnf', [status(esa)], [t1_boole])).
% 1.72/1.93  thf('119', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.72/1.93      inference('sup+', [status(thm)], ['117', '118'])).
% 1.72/1.93  thf('120', plain,
% 1.72/1.93      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.72/1.93          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('demod', [status(thm)], ['116', '119'])).
% 1.72/1.93  thf('121', plain,
% 1.72/1.93      (((k1_tops_1 @ sk_A @ sk_B)
% 1.72/1.93         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('demod', [status(thm)], ['45', '46', '51'])).
% 1.72/1.93  thf('122', plain,
% 1.72/1.93      (![X29 : $i, X30 : $i]:
% 1.72/1.93         ((k2_xboole_0 @ (k6_subset_1 @ X29 @ X30) @ (k3_xboole_0 @ X29 @ X30))
% 1.72/1.93           = (X29))),
% 1.72/1.93      inference('demod', [status(thm)], ['107', '108', '113'])).
% 1.72/1.93  thf('123', plain,
% 1.72/1.93      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.72/1.93         (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 1.72/1.93      inference('sup+', [status(thm)], ['121', '122'])).
% 1.72/1.93  thf('124', plain,
% 1.72/1.93      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.72/1.93          = (sk_B)))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['120', '123'])).
% 1.72/1.93  thf('125', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.72/1.93      inference('sup+', [status(thm)], ['111', '112'])).
% 1.72/1.93  thf('126', plain,
% 1.72/1.93      (![X31 : $i, X32 : $i]:
% 1.72/1.93         ((k2_xboole_0 @ X31 @ (k2_xboole_0 @ X31 @ X32))
% 1.72/1.93           = (k2_xboole_0 @ X31 @ X32))),
% 1.72/1.93      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.72/1.93  thf('127', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]:
% 1.72/1.93         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.72/1.93           = (k2_xboole_0 @ X0 @ X1))),
% 1.72/1.93      inference('sup+', [status(thm)], ['125', '126'])).
% 1.72/1.93  thf('128', plain,
% 1.72/1.93      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.72/1.93          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.72/1.93             (k1_tops_1 @ sk_A @ sk_B))))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['124', '127'])).
% 1.72/1.93  thf('129', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.72/1.93      inference('sup+', [status(thm)], ['111', '112'])).
% 1.72/1.93  thf('130', plain,
% 1.72/1.93      (((k2_pre_topc @ sk_A @ sk_B)
% 1.72/1.93         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.72/1.93      inference('sup+', [status(thm)], ['18', '23'])).
% 1.72/1.93  thf('131', plain,
% 1.72/1.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.72/1.93      inference('sup+', [status(thm)], ['111', '112'])).
% 1.72/1.93  thf('132', plain,
% 1.72/1.93      ((((k2_pre_topc @ sk_A @ sk_B)
% 1.72/1.93          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.72/1.93             (k2_tops_1 @ sk_A @ sk_B))))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 1.72/1.93  thf('133', plain,
% 1.72/1.93      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.72/1.93          = (sk_B)))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['120', '123'])).
% 1.72/1.93  thf('134', plain,
% 1.72/1.93      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup+', [status(thm)], ['132', '133'])).
% 1.72/1.93  thf('135', plain,
% 1.72/1.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('136', plain,
% 1.72/1.93      (![X60 : $i, X61 : $i]:
% 1.72/1.93         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 1.72/1.93          | ~ (v2_pre_topc @ X61)
% 1.72/1.93          | ((k2_pre_topc @ X61 @ X60) != (X60))
% 1.72/1.93          | (v4_pre_topc @ X60 @ X61)
% 1.72/1.93          | ~ (l1_pre_topc @ X61))),
% 1.72/1.93      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.72/1.93  thf('137', plain,
% 1.72/1.93      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.93        | (v4_pre_topc @ sk_B @ sk_A)
% 1.72/1.93        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.72/1.93        | ~ (v2_pre_topc @ sk_A))),
% 1.72/1.93      inference('sup-', [status(thm)], ['135', '136'])).
% 1.72/1.93  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 1.72/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.93  thf('140', plain,
% 1.72/1.93      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.72/1.93      inference('demod', [status(thm)], ['137', '138', '139'])).
% 1.72/1.93  thf('141', plain,
% 1.72/1.93      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('sup-', [status(thm)], ['134', '140'])).
% 1.72/1.93  thf('142', plain,
% 1.72/1.93      (((v4_pre_topc @ sk_B @ sk_A))
% 1.72/1.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.72/1.93      inference('simplify', [status(thm)], ['141'])).
% 1.72/1.93  thf('143', plain,
% 1.72/1.93      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.72/1.93      inference('split', [status(esa)], ['0'])).
% 1.72/1.93  thf('144', plain,
% 1.72/1.93      (~
% 1.72/1.93       (((k2_tops_1 @ sk_A @ sk_B)
% 1.72/1.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.93             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.72/1.93       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.72/1.93      inference('sup-', [status(thm)], ['142', '143'])).
% 1.72/1.93  thf('145', plain, ($false),
% 1.72/1.93      inference('sat_resolution*', [status(thm)], ['1', '67', '68', '144'])).
% 1.72/1.93  
% 1.72/1.93  % SZS output end Refutation
% 1.72/1.93  
% 1.72/1.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
