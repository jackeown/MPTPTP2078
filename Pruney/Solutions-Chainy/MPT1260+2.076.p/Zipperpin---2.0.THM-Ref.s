%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fPNk2MuMOH

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:35 EST 2020

% Result     : Theorem 6.10s
% Output     : Refutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :  201 (1072 expanded)
%              Number of leaves         :   36 ( 320 expanded)
%              Depth                    :   19
%              Number of atoms          : 2037 (13919 expanded)
%              Number of equality atoms :  136 ( 748 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 @ ( k2_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('29',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ X29 @ ( k2_pre_topc @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('51',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','56'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('62',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X35 )
      | ( ( k1_tops_1 @ X35 @ X36 )
        = X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('63',plain,
    ( ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( v3_pre_topc @ X36 @ X35 )
        | ( ( k1_tops_1 @ X35 @ X36 )
          = X36 ) )
   <= ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( v3_pre_topc @ X36 @ X35 )
        | ( ( k1_tops_1 @ X35 @ X36 )
          = X36 ) ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) )
   <= ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(split,[status(esa)],['62'])).

thf('66',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ~ ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( v3_pre_topc @ X36 @ X35 )
        | ( ( k1_tops_1 @ X35 @ X36 )
          = X36 ) )
    | ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(split,[status(esa)],['62'])).

thf('71',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X35 )
      | ( ( k1_tops_1 @ X35 @ X36 )
        = X36 ) ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X35 )
      | ( ( k1_tops_1 @ X35 @ X36 )
        = X36 ) ) ),
    inference(simpl_trail,[status(thm)],['63','71'])).

thf('73',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('78',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ X33 ) @ ( k1_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('83',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['76','83'])).

thf('85',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('86',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('88',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['58'])).

thf('89',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('95',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['59','93','94'])).

thf('96',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['57','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('99',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X23 @ X21 )
        = ( k9_subset_1 @ X22 @ X23 @ ( k3_subset_1 @ X22 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('105',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('109',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X14 @ X13 @ X13 )
        = X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['96','111'])).

thf('113',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('114',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['59','93','94'])).

thf('115',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['113','114'])).

thf('116',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['57','95'])).

thf('117',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['112','115','116'])).

thf('118',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['7','117'])).

thf('119',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('120',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('123',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('128',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','132'])).

thf('134',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['134','139'])).

thf('141',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k1_tops_1 @ X38 @ X37 )
       != X37 )
      | ( v3_pre_topc @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('142',plain,
    ( ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 )
        | ( ( k1_tops_1 @ X38 @ X37 )
         != X37 )
        | ( v3_pre_topc @ X37 @ X38 ) )
   <= ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 )
        | ( ( k1_tops_1 @ X38 @ X37 )
         != X37 )
        | ( v3_pre_topc @ X37 @ X38 ) ) ),
    inference(split,[status(esa)],['141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) )
   <= ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference(split,[status(esa)],['141'])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ~ ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ! [X37: $i,X38: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
        | ~ ( l1_pre_topc @ X38 )
        | ~ ( v2_pre_topc @ X38 )
        | ( ( k1_tops_1 @ X38 @ X37 )
         != X37 )
        | ( v3_pre_topc @ X37 @ X38 ) )
    | ! [X35: $i,X36: $i] :
        ( ~ ( l1_pre_topc @ X35 )
        | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference(split,[status(esa)],['141'])).

thf('149',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( ( k1_tops_1 @ X38 @ X37 )
       != X37 )
      | ( v3_pre_topc @ X37 @ X38 ) ) ),
    inference('sat_resolution*',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( ( k1_tops_1 @ X38 @ X37 )
       != X37 )
      | ( v3_pre_topc @ X37 @ X38 ) ) ),
    inference(simpl_trail,[status(thm)],['142','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','150'])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_B @ sk_B ) )
    | ( v3_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['133','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','132'])).

thf('157',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','132'])).

thf('158',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('160',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['59','93'])).

thf('161',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['159','160'])).

thf('162',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != sk_B ),
    inference(clc,[status(thm)],['158','161'])).

thf('163',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fPNk2MuMOH
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:26:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 6.10/6.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.10/6.31  % Solved by: fo/fo7.sh
% 6.10/6.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.10/6.31  % done 7229 iterations in 5.849s
% 6.10/6.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.10/6.31  % SZS output start Refutation
% 6.10/6.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.10/6.31  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 6.10/6.31  thf(sk_B_type, type, sk_B: $i).
% 6.10/6.31  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 6.10/6.31  thf(sk_A_type, type, sk_A: $i).
% 6.10/6.31  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 6.10/6.31  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 6.10/6.31  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 6.10/6.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.10/6.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.10/6.31  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 6.10/6.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.10/6.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.10/6.31  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 6.10/6.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.10/6.31  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 6.10/6.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.10/6.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.10/6.31  thf(t76_tops_1, conjecture,
% 6.10/6.31    (![A:$i]:
% 6.10/6.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.10/6.31       ( ![B:$i]:
% 6.10/6.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.10/6.31           ( ( v3_pre_topc @ B @ A ) <=>
% 6.10/6.31             ( ( k2_tops_1 @ A @ B ) =
% 6.10/6.31               ( k7_subset_1 @
% 6.10/6.31                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 6.10/6.31  thf(zf_stmt_0, negated_conjecture,
% 6.10/6.31    (~( ![A:$i]:
% 6.10/6.31        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.10/6.31          ( ![B:$i]:
% 6.10/6.31            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.10/6.31              ( ( v3_pre_topc @ B @ A ) <=>
% 6.10/6.31                ( ( k2_tops_1 @ A @ B ) =
% 6.10/6.31                  ( k7_subset_1 @
% 6.10/6.31                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 6.10/6.31    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 6.10/6.31  thf('0', plain,
% 6.10/6.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf(t74_tops_1, axiom,
% 6.10/6.31    (![A:$i]:
% 6.10/6.31     ( ( l1_pre_topc @ A ) =>
% 6.10/6.31       ( ![B:$i]:
% 6.10/6.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.10/6.31           ( ( k1_tops_1 @ A @ B ) =
% 6.10/6.31             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 6.10/6.31  thf('1', plain,
% 6.10/6.31      (![X39 : $i, X40 : $i]:
% 6.10/6.31         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 6.10/6.31          | ((k1_tops_1 @ X40 @ X39)
% 6.10/6.31              = (k7_subset_1 @ (u1_struct_0 @ X40) @ X39 @ 
% 6.10/6.31                 (k2_tops_1 @ X40 @ X39)))
% 6.10/6.31          | ~ (l1_pre_topc @ X40))),
% 6.10/6.31      inference('cnf', [status(esa)], [t74_tops_1])).
% 6.10/6.31  thf('2', plain,
% 6.10/6.31      ((~ (l1_pre_topc @ sk_A)
% 6.10/6.31        | ((k1_tops_1 @ sk_A @ sk_B)
% 6.10/6.31            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 6.10/6.31               (k2_tops_1 @ sk_A @ sk_B))))),
% 6.10/6.31      inference('sup-', [status(thm)], ['0', '1'])).
% 6.10/6.31  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('4', plain,
% 6.10/6.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf(redefinition_k7_subset_1, axiom,
% 6.10/6.31    (![A:$i,B:$i,C:$i]:
% 6.10/6.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.10/6.31       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 6.10/6.31  thf('5', plain,
% 6.10/6.31      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.10/6.31         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 6.10/6.31          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 6.10/6.31      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.10/6.31  thf('6', plain,
% 6.10/6.31      (![X0 : $i]:
% 6.10/6.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 6.10/6.31           = (k4_xboole_0 @ sk_B @ X0))),
% 6.10/6.31      inference('sup-', [status(thm)], ['4', '5'])).
% 6.10/6.31  thf('7', plain,
% 6.10/6.31      (((k1_tops_1 @ sk_A @ sk_B)
% 6.10/6.31         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 6.10/6.31      inference('demod', [status(thm)], ['2', '3', '6'])).
% 6.10/6.31  thf('8', plain,
% 6.10/6.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf(dt_k2_pre_topc, axiom,
% 6.10/6.31    (![A:$i,B:$i]:
% 6.10/6.31     ( ( ( l1_pre_topc @ A ) & 
% 6.10/6.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.10/6.31       ( m1_subset_1 @
% 6.10/6.31         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.10/6.31  thf('9', plain,
% 6.10/6.31      (![X27 : $i, X28 : $i]:
% 6.10/6.31         (~ (l1_pre_topc @ X27)
% 6.10/6.31          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 6.10/6.31          | (m1_subset_1 @ (k2_pre_topc @ X27 @ X28) @ 
% 6.10/6.31             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 6.10/6.31      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 6.10/6.31  thf('10', plain,
% 6.10/6.31      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.10/6.31        | ~ (l1_pre_topc @ sk_A))),
% 6.10/6.31      inference('sup-', [status(thm)], ['8', '9'])).
% 6.10/6.31  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('12', plain,
% 6.10/6.31      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.31      inference('demod', [status(thm)], ['10', '11'])).
% 6.10/6.31  thf('13', plain,
% 6.10/6.31      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.10/6.31         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 6.10/6.31          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 6.10/6.31      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.10/6.31  thf('14', plain,
% 6.10/6.31      (![X0 : $i]:
% 6.10/6.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 6.10/6.31      inference('sup-', [status(thm)], ['12', '13'])).
% 6.10/6.31  thf('15', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 6.10/6.31        | (v3_pre_topc @ sk_B @ sk_A))),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('16', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('split', [status(esa)], ['15'])).
% 6.10/6.31  thf('17', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('sup+', [status(thm)], ['14', '16'])).
% 6.10/6.31  thf(t48_xboole_1, axiom,
% 6.10/6.31    (![A:$i,B:$i]:
% 6.10/6.31     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.10/6.31  thf('18', plain,
% 6.10/6.31      (![X2 : $i, X3 : $i]:
% 6.10/6.31         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 6.10/6.31           = (k3_xboole_0 @ X2 @ X3))),
% 6.10/6.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.10/6.31  thf('19', plain,
% 6.10/6.31      (![X2 : $i, X3 : $i]:
% 6.10/6.31         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 6.10/6.31           = (k3_xboole_0 @ X2 @ X3))),
% 6.10/6.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.10/6.31  thf('20', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 6.10/6.31           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.10/6.31      inference('sup+', [status(thm)], ['18', '19'])).
% 6.10/6.31  thf(t47_xboole_1, axiom,
% 6.10/6.31    (![A:$i,B:$i]:
% 6.10/6.31     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 6.10/6.31  thf('21', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 6.10/6.31           = (k4_xboole_0 @ X0 @ X1))),
% 6.10/6.31      inference('cnf', [status(esa)], [t47_xboole_1])).
% 6.10/6.31  thf('22', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         ((k4_xboole_0 @ X1 @ X0)
% 6.10/6.31           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.10/6.31      inference('demod', [status(thm)], ['20', '21'])).
% 6.10/6.31  thf('23', plain,
% 6.10/6.31      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 6.10/6.31          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31             (k2_tops_1 @ sk_A @ sk_B))))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('sup+', [status(thm)], ['17', '22'])).
% 6.10/6.31  thf('24', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('sup+', [status(thm)], ['14', '16'])).
% 6.10/6.31  thf('25', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31             (k2_tops_1 @ sk_A @ sk_B))))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('demod', [status(thm)], ['23', '24'])).
% 6.10/6.31  thf('26', plain,
% 6.10/6.31      (![X2 : $i, X3 : $i]:
% 6.10/6.31         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 6.10/6.31           = (k3_xboole_0 @ X2 @ X3))),
% 6.10/6.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.10/6.31  thf(dt_k2_subset_1, axiom,
% 6.10/6.31    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 6.10/6.31  thf('27', plain,
% 6.10/6.31      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 6.10/6.31      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 6.10/6.31  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 6.10/6.31  thf('28', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 6.10/6.31      inference('cnf', [status(esa)], [d4_subset_1])).
% 6.10/6.31  thf('29', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 6.10/6.31      inference('demod', [status(thm)], ['27', '28'])).
% 6.10/6.31  thf(dt_k7_subset_1, axiom,
% 6.10/6.31    (![A:$i,B:$i,C:$i]:
% 6.10/6.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.10/6.31       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.10/6.31  thf('30', plain,
% 6.10/6.31      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.10/6.31         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 6.10/6.31          | (m1_subset_1 @ (k7_subset_1 @ X11 @ X10 @ X12) @ 
% 6.10/6.31             (k1_zfmisc_1 @ X11)))),
% 6.10/6.31      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 6.10/6.31  thf('31', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 6.10/6.31      inference('sup-', [status(thm)], ['29', '30'])).
% 6.10/6.31  thf('32', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 6.10/6.31      inference('demod', [status(thm)], ['27', '28'])).
% 6.10/6.31  thf('33', plain,
% 6.10/6.31      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.10/6.31         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 6.10/6.31          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 6.10/6.31      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.10/6.31  thf('34', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 6.10/6.31      inference('sup-', [status(thm)], ['32', '33'])).
% 6.10/6.31  thf('35', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 6.10/6.31      inference('demod', [status(thm)], ['31', '34'])).
% 6.10/6.31  thf('36', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 6.10/6.31      inference('sup+', [status(thm)], ['26', '35'])).
% 6.10/6.31  thf(d5_subset_1, axiom,
% 6.10/6.31    (![A:$i,B:$i]:
% 6.10/6.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.10/6.31       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 6.10/6.31  thf('37', plain,
% 6.10/6.31      (![X5 : $i, X6 : $i]:
% 6.10/6.31         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 6.10/6.31          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 6.10/6.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.10/6.31  thf('38', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 6.10/6.31           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.10/6.31      inference('sup-', [status(thm)], ['36', '37'])).
% 6.10/6.31  thf('39', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 6.10/6.31           = (k4_xboole_0 @ X0 @ X1))),
% 6.10/6.31      inference('cnf', [status(esa)], [t47_xboole_1])).
% 6.10/6.31  thf('40', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         ((k3_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 6.10/6.31           = (k4_xboole_0 @ X1 @ X0))),
% 6.10/6.31      inference('sup+', [status(thm)], ['38', '39'])).
% 6.10/6.31  thf('41', plain,
% 6.10/6.31      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 6.10/6.31          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31             (k2_tops_1 @ sk_A @ sk_B))))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('sup+', [status(thm)], ['25', '40'])).
% 6.10/6.31  thf('42', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('sup+', [status(thm)], ['14', '16'])).
% 6.10/6.31  thf('43', plain,
% 6.10/6.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf(t48_pre_topc, axiom,
% 6.10/6.31    (![A:$i]:
% 6.10/6.31     ( ( l1_pre_topc @ A ) =>
% 6.10/6.31       ( ![B:$i]:
% 6.10/6.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.10/6.31           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 6.10/6.31  thf('44', plain,
% 6.10/6.31      (![X29 : $i, X30 : $i]:
% 6.10/6.31         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 6.10/6.31          | (r1_tarski @ X29 @ (k2_pre_topc @ X30 @ X29))
% 6.10/6.31          | ~ (l1_pre_topc @ X30))),
% 6.10/6.31      inference('cnf', [status(esa)], [t48_pre_topc])).
% 6.10/6.31  thf('45', plain,
% 6.10/6.31      ((~ (l1_pre_topc @ sk_A)
% 6.10/6.31        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.10/6.31      inference('sup-', [status(thm)], ['43', '44'])).
% 6.10/6.31  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('47', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 6.10/6.31      inference('demod', [status(thm)], ['45', '46'])).
% 6.10/6.31  thf(t3_subset, axiom,
% 6.10/6.31    (![A:$i,B:$i]:
% 6.10/6.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.10/6.31  thf('48', plain,
% 6.10/6.31      (![X24 : $i, X26 : $i]:
% 6.10/6.31         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 6.10/6.31      inference('cnf', [status(esa)], [t3_subset])).
% 6.10/6.31  thf('49', plain,
% 6.10/6.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.10/6.31      inference('sup-', [status(thm)], ['47', '48'])).
% 6.10/6.31  thf('50', plain,
% 6.10/6.31      (![X5 : $i, X6 : $i]:
% 6.10/6.31         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 6.10/6.31          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 6.10/6.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.10/6.31  thf('51', plain,
% 6.10/6.31      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 6.10/6.31         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 6.10/6.31      inference('sup-', [status(thm)], ['49', '50'])).
% 6.10/6.31  thf('52', plain,
% 6.10/6.31      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 6.10/6.31          = (k2_tops_1 @ sk_A @ sk_B)))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('sup+', [status(thm)], ['42', '51'])).
% 6.10/6.31  thf('53', plain,
% 6.10/6.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.10/6.31      inference('sup-', [status(thm)], ['47', '48'])).
% 6.10/6.31  thf(involutiveness_k3_subset_1, axiom,
% 6.10/6.31    (![A:$i,B:$i]:
% 6.10/6.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.10/6.31       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 6.10/6.31  thf('54', plain,
% 6.10/6.31      (![X16 : $i, X17 : $i]:
% 6.10/6.31         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 6.10/6.31          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 6.10/6.31      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 6.10/6.31  thf('55', plain,
% 6.10/6.31      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 6.10/6.31      inference('sup-', [status(thm)], ['53', '54'])).
% 6.10/6.31  thf('56', plain,
% 6.10/6.31      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 6.10/6.31          = (sk_B)))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('sup+', [status(thm)], ['52', '55'])).
% 6.10/6.31  thf('57', plain,
% 6.10/6.31      ((((sk_B)
% 6.10/6.31          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31             (k2_tops_1 @ sk_A @ sk_B))))
% 6.10/6.31         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('demod', [status(thm)], ['41', '56'])).
% 6.10/6.31  thf('58', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 6.10/6.31        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('59', plain,
% 6.10/6.31      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 6.10/6.31       ~
% 6.10/6.31       (((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 6.10/6.31      inference('split', [status(esa)], ['58'])).
% 6.10/6.31  thf('60', plain,
% 6.10/6.31      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.10/6.31      inference('split', [status(esa)], ['15'])).
% 6.10/6.31  thf('61', plain,
% 6.10/6.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf(t55_tops_1, axiom,
% 6.10/6.31    (![A:$i]:
% 6.10/6.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.10/6.31       ( ![B:$i]:
% 6.10/6.31         ( ( l1_pre_topc @ B ) =>
% 6.10/6.31           ( ![C:$i]:
% 6.10/6.31             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.10/6.31               ( ![D:$i]:
% 6.10/6.31                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 6.10/6.31                   ( ( ( v3_pre_topc @ D @ B ) =>
% 6.10/6.31                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 6.10/6.31                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 6.10/6.31                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 6.10/6.31  thf('62', plain,
% 6.10/6.31      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 6.10/6.31         (~ (l1_pre_topc @ X35)
% 6.10/6.31          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 6.10/6.31          | ~ (v3_pre_topc @ X36 @ X35)
% 6.10/6.31          | ((k1_tops_1 @ X35 @ X36) = (X36))
% 6.10/6.31          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.31          | ~ (l1_pre_topc @ X38)
% 6.10/6.31          | ~ (v2_pre_topc @ X38))),
% 6.10/6.31      inference('cnf', [status(esa)], [t55_tops_1])).
% 6.10/6.31  thf('63', plain,
% 6.10/6.31      ((![X35 : $i, X36 : $i]:
% 6.10/6.31          (~ (l1_pre_topc @ X35)
% 6.10/6.31           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 6.10/6.31           | ~ (v3_pre_topc @ X36 @ X35)
% 6.10/6.31           | ((k1_tops_1 @ X35 @ X36) = (X36))))
% 6.10/6.31         <= ((![X35 : $i, X36 : $i]:
% 6.10/6.31                (~ (l1_pre_topc @ X35)
% 6.10/6.31                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 6.10/6.31                 | ~ (v3_pre_topc @ X36 @ X35)
% 6.10/6.31                 | ((k1_tops_1 @ X35 @ X36) = (X36)))))),
% 6.10/6.31      inference('split', [status(esa)], ['62'])).
% 6.10/6.31  thf('64', plain,
% 6.10/6.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('65', plain,
% 6.10/6.31      ((![X37 : $i, X38 : $i]:
% 6.10/6.31          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.31           | ~ (l1_pre_topc @ X38)
% 6.10/6.31           | ~ (v2_pre_topc @ X38)))
% 6.10/6.31         <= ((![X37 : $i, X38 : $i]:
% 6.10/6.31                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.31                 | ~ (l1_pre_topc @ X38)
% 6.10/6.31                 | ~ (v2_pre_topc @ X38))))),
% 6.10/6.31      inference('split', [status(esa)], ['62'])).
% 6.10/6.31  thf('66', plain,
% 6.10/6.31      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 6.10/6.31         <= ((![X37 : $i, X38 : $i]:
% 6.10/6.31                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.31                 | ~ (l1_pre_topc @ X38)
% 6.10/6.31                 | ~ (v2_pre_topc @ X38))))),
% 6.10/6.31      inference('sup-', [status(thm)], ['64', '65'])).
% 6.10/6.31  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('69', plain,
% 6.10/6.31      (~
% 6.10/6.31       (![X37 : $i, X38 : $i]:
% 6.10/6.31          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.31           | ~ (l1_pre_topc @ X38)
% 6.10/6.31           | ~ (v2_pre_topc @ X38)))),
% 6.10/6.31      inference('demod', [status(thm)], ['66', '67', '68'])).
% 6.10/6.31  thf('70', plain,
% 6.10/6.31      ((![X35 : $i, X36 : $i]:
% 6.10/6.31          (~ (l1_pre_topc @ X35)
% 6.10/6.31           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 6.10/6.31           | ~ (v3_pre_topc @ X36 @ X35)
% 6.10/6.31           | ((k1_tops_1 @ X35 @ X36) = (X36)))) | 
% 6.10/6.31       (![X37 : $i, X38 : $i]:
% 6.10/6.31          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.31           | ~ (l1_pre_topc @ X38)
% 6.10/6.31           | ~ (v2_pre_topc @ X38)))),
% 6.10/6.31      inference('split', [status(esa)], ['62'])).
% 6.10/6.31  thf('71', plain,
% 6.10/6.31      ((![X35 : $i, X36 : $i]:
% 6.10/6.31          (~ (l1_pre_topc @ X35)
% 6.10/6.31           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 6.10/6.31           | ~ (v3_pre_topc @ X36 @ X35)
% 6.10/6.31           | ((k1_tops_1 @ X35 @ X36) = (X36))))),
% 6.10/6.31      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 6.10/6.31  thf('72', plain,
% 6.10/6.31      (![X35 : $i, X36 : $i]:
% 6.10/6.31         (~ (l1_pre_topc @ X35)
% 6.10/6.31          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 6.10/6.31          | ~ (v3_pre_topc @ X36 @ X35)
% 6.10/6.31          | ((k1_tops_1 @ X35 @ X36) = (X36)))),
% 6.10/6.31      inference('simpl_trail', [status(thm)], ['63', '71'])).
% 6.10/6.31  thf('73', plain,
% 6.10/6.31      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 6.10/6.31        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 6.10/6.31        | ~ (l1_pre_topc @ sk_A))),
% 6.10/6.31      inference('sup-', [status(thm)], ['61', '72'])).
% 6.10/6.31  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('75', plain,
% 6.10/6.31      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 6.10/6.31      inference('demod', [status(thm)], ['73', '74'])).
% 6.10/6.31  thf('76', plain,
% 6.10/6.31      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 6.10/6.31         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.10/6.31      inference('sup-', [status(thm)], ['60', '75'])).
% 6.10/6.31  thf('77', plain,
% 6.10/6.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf(l78_tops_1, axiom,
% 6.10/6.31    (![A:$i]:
% 6.10/6.31     ( ( l1_pre_topc @ A ) =>
% 6.10/6.31       ( ![B:$i]:
% 6.10/6.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.10/6.31           ( ( k2_tops_1 @ A @ B ) =
% 6.10/6.31             ( k7_subset_1 @
% 6.10/6.31               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 6.10/6.31               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 6.10/6.31  thf('78', plain,
% 6.10/6.31      (![X33 : $i, X34 : $i]:
% 6.10/6.31         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 6.10/6.31          | ((k2_tops_1 @ X34 @ X33)
% 6.10/6.31              = (k7_subset_1 @ (u1_struct_0 @ X34) @ 
% 6.10/6.31                 (k2_pre_topc @ X34 @ X33) @ (k1_tops_1 @ X34 @ X33)))
% 6.10/6.31          | ~ (l1_pre_topc @ X34))),
% 6.10/6.31      inference('cnf', [status(esa)], [l78_tops_1])).
% 6.10/6.31  thf('79', plain,
% 6.10/6.31      ((~ (l1_pre_topc @ sk_A)
% 6.10/6.31        | ((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 6.10/6.31      inference('sup-', [status(thm)], ['77', '78'])).
% 6.10/6.31  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 6.10/6.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.31  thf('81', plain,
% 6.10/6.31      (((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31            (k1_tops_1 @ sk_A @ sk_B)))),
% 6.10/6.31      inference('demod', [status(thm)], ['79', '80'])).
% 6.10/6.31  thf('82', plain,
% 6.10/6.31      (![X0 : $i]:
% 6.10/6.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 6.10/6.31      inference('sup-', [status(thm)], ['12', '13'])).
% 6.10/6.31  thf('83', plain,
% 6.10/6.31      (((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31            (k1_tops_1 @ sk_A @ sk_B)))),
% 6.10/6.31      inference('demod', [status(thm)], ['81', '82'])).
% 6.10/6.31  thf('84', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 6.10/6.31         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.10/6.31      inference('sup+', [status(thm)], ['76', '83'])).
% 6.10/6.31  thf('85', plain,
% 6.10/6.31      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 6.10/6.31         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 6.10/6.31      inference('sup-', [status(thm)], ['49', '50'])).
% 6.10/6.31  thf('86', plain,
% 6.10/6.31      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 6.10/6.31          = (k2_tops_1 @ sk_A @ sk_B)))
% 6.10/6.31         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 6.10/6.31      inference('sup+', [status(thm)], ['84', '85'])).
% 6.10/6.31  thf('87', plain,
% 6.10/6.31      (![X0 : $i]:
% 6.10/6.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 6.10/6.31      inference('sup-', [status(thm)], ['12', '13'])).
% 6.10/6.31  thf('88', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 6.10/6.31         <= (~
% 6.10/6.31             (((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('split', [status(esa)], ['58'])).
% 6.10/6.31  thf('89', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 6.10/6.31         <= (~
% 6.10/6.31             (((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('sup-', [status(thm)], ['87', '88'])).
% 6.10/6.31  thf('90', plain,
% 6.10/6.31      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 6.10/6.31         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 6.10/6.31      inference('sup-', [status(thm)], ['49', '50'])).
% 6.10/6.31  thf('91', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          != (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 6.10/6.31         <= (~
% 6.10/6.31             (((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.31      inference('demod', [status(thm)], ['89', '90'])).
% 6.10/6.31  thf('92', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 6.10/6.31         <= (~
% 6.10/6.31             (((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 6.10/6.31             ((v3_pre_topc @ sk_B @ sk_A)))),
% 6.10/6.31      inference('sup-', [status(thm)], ['86', '91'])).
% 6.10/6.31  thf('93', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 6.10/6.31       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 6.10/6.31      inference('simplify', [status(thm)], ['92'])).
% 6.10/6.31  thf('94', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 6.10/6.31       ((v3_pre_topc @ sk_B @ sk_A))),
% 6.10/6.31      inference('split', [status(esa)], ['15'])).
% 6.10/6.31  thf('95', plain,
% 6.10/6.31      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.31          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.31             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 6.10/6.31      inference('sat_resolution*', [status(thm)], ['59', '93', '94'])).
% 6.10/6.31  thf('96', plain,
% 6.10/6.31      (((sk_B)
% 6.10/6.31         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.31            (k2_tops_1 @ sk_A @ sk_B)))),
% 6.10/6.31      inference('simpl_trail', [status(thm)], ['57', '95'])).
% 6.10/6.31  thf('97', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 6.10/6.31      inference('demod', [status(thm)], ['31', '34'])).
% 6.10/6.31  thf('98', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i]:
% 6.10/6.31         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 6.10/6.31      inference('sup+', [status(thm)], ['26', '35'])).
% 6.10/6.31  thf(t32_subset_1, axiom,
% 6.10/6.31    (![A:$i,B:$i]:
% 6.10/6.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.10/6.31       ( ![C:$i]:
% 6.10/6.31         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.10/6.31           ( ( k7_subset_1 @ A @ B @ C ) =
% 6.10/6.31             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 6.10/6.31  thf('99', plain,
% 6.10/6.31      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.10/6.31         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 6.10/6.31          | ((k7_subset_1 @ X22 @ X23 @ X21)
% 6.10/6.31              = (k9_subset_1 @ X22 @ X23 @ (k3_subset_1 @ X22 @ X21)))
% 6.10/6.31          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 6.10/6.31      inference('cnf', [status(esa)], [t32_subset_1])).
% 6.10/6.31  thf('100', plain,
% 6.10/6.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.10/6.31         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 6.10/6.31          | ((k7_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X0 @ X1))
% 6.10/6.32              = (k9_subset_1 @ X0 @ X2 @ 
% 6.10/6.32                 (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))))),
% 6.10/6.32      inference('sup-', [status(thm)], ['98', '99'])).
% 6.10/6.32  thf('101', plain,
% 6.10/6.32      (![X0 : $i, X1 : $i]:
% 6.10/6.32         ((k3_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 6.10/6.32           = (k4_xboole_0 @ X1 @ X0))),
% 6.10/6.32      inference('sup+', [status(thm)], ['38', '39'])).
% 6.10/6.32  thf('102', plain,
% 6.10/6.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.10/6.32         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 6.10/6.32          | ((k7_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X0 @ X1))
% 6.10/6.32              = (k9_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 6.10/6.32      inference('demod', [status(thm)], ['100', '101'])).
% 6.10/6.32  thf('103', plain,
% 6.10/6.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.10/6.32         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 6.10/6.32           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 6.10/6.32              (k4_xboole_0 @ X0 @ X2)))),
% 6.10/6.32      inference('sup-', [status(thm)], ['97', '102'])).
% 6.10/6.32  thf('104', plain,
% 6.10/6.32      (![X0 : $i, X1 : $i]:
% 6.10/6.32         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 6.10/6.32      inference('demod', [status(thm)], ['31', '34'])).
% 6.10/6.32  thf('105', plain,
% 6.10/6.32      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.10/6.32         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 6.10/6.32          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 6.10/6.32      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.10/6.32  thf('106', plain,
% 6.10/6.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.10/6.32         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 6.10/6.32           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 6.10/6.32      inference('sup-', [status(thm)], ['104', '105'])).
% 6.10/6.32  thf('107', plain,
% 6.10/6.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.10/6.32         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 6.10/6.32           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 6.10/6.32              (k4_xboole_0 @ X0 @ X2)))),
% 6.10/6.32      inference('demod', [status(thm)], ['103', '106'])).
% 6.10/6.32  thf('108', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 6.10/6.32      inference('demod', [status(thm)], ['27', '28'])).
% 6.10/6.32  thf(idempotence_k9_subset_1, axiom,
% 6.10/6.32    (![A:$i,B:$i,C:$i]:
% 6.10/6.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.10/6.32       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 6.10/6.32  thf('109', plain,
% 6.10/6.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.10/6.32         (((k9_subset_1 @ X14 @ X13 @ X13) = (X13))
% 6.10/6.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 6.10/6.32      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 6.10/6.32  thf('110', plain,
% 6.10/6.32      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 6.10/6.32      inference('sup-', [status(thm)], ['108', '109'])).
% 6.10/6.32  thf('111', plain,
% 6.10/6.32      (![X0 : $i, X1 : $i]:
% 6.10/6.32         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 6.10/6.32           = (k4_xboole_0 @ X1 @ X0))),
% 6.10/6.32      inference('sup+', [status(thm)], ['107', '110'])).
% 6.10/6.32  thf('112', plain,
% 6.10/6.32      (((k4_xboole_0 @ sk_B @ 
% 6.10/6.32         (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))
% 6.10/6.32         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.32            (k2_tops_1 @ sk_A @ sk_B)))),
% 6.10/6.32      inference('sup+', [status(thm)], ['96', '111'])).
% 6.10/6.32  thf('113', plain,
% 6.10/6.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.32          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.32             (k2_tops_1 @ sk_A @ sk_B))))
% 6.10/6.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 6.10/6.32      inference('demod', [status(thm)], ['23', '24'])).
% 6.10/6.32  thf('114', plain,
% 6.10/6.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 6.10/6.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 6.10/6.32      inference('sat_resolution*', [status(thm)], ['59', '93', '94'])).
% 6.10/6.32  thf('115', plain,
% 6.10/6.32      (((k2_tops_1 @ sk_A @ sk_B)
% 6.10/6.32         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.32            (k2_tops_1 @ sk_A @ sk_B)))),
% 6.10/6.32      inference('simpl_trail', [status(thm)], ['113', '114'])).
% 6.10/6.32  thf('116', plain,
% 6.10/6.32      (((sk_B)
% 6.10/6.32         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.10/6.32            (k2_tops_1 @ sk_A @ sk_B)))),
% 6.10/6.32      inference('simpl_trail', [status(thm)], ['57', '95'])).
% 6.10/6.32  thf('117', plain,
% 6.10/6.32      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 6.10/6.32      inference('demod', [status(thm)], ['112', '115', '116'])).
% 6.10/6.32  thf('118', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 6.10/6.32      inference('sup+', [status(thm)], ['7', '117'])).
% 6.10/6.32  thf('119', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 6.10/6.32      inference('demod', [status(thm)], ['27', '28'])).
% 6.10/6.32  thf('120', plain,
% 6.10/6.32      (![X16 : $i, X17 : $i]:
% 6.10/6.32         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 6.10/6.32          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 6.10/6.32      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 6.10/6.32  thf('121', plain,
% 6.10/6.32      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 6.10/6.32      inference('sup-', [status(thm)], ['119', '120'])).
% 6.10/6.32  thf('122', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 6.10/6.32      inference('demod', [status(thm)], ['27', '28'])).
% 6.10/6.32  thf(dt_k3_subset_1, axiom,
% 6.10/6.32    (![A:$i,B:$i]:
% 6.10/6.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.10/6.32       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.10/6.32  thf('123', plain,
% 6.10/6.32      (![X8 : $i, X9 : $i]:
% 6.10/6.32         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 6.10/6.32          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 6.10/6.32      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 6.10/6.32  thf('124', plain,
% 6.10/6.32      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 6.10/6.32      inference('sup-', [status(thm)], ['122', '123'])).
% 6.10/6.32  thf('125', plain,
% 6.10/6.32      (![X5 : $i, X6 : $i]:
% 6.10/6.32         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 6.10/6.32          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 6.10/6.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.10/6.32  thf('126', plain,
% 6.10/6.32      (![X0 : $i]:
% 6.10/6.32         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0))
% 6.10/6.32           = (k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0)))),
% 6.10/6.32      inference('sup-', [status(thm)], ['124', '125'])).
% 6.10/6.32  thf('127', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 6.10/6.32      inference('demod', [status(thm)], ['27', '28'])).
% 6.10/6.32  thf('128', plain,
% 6.10/6.32      (![X5 : $i, X6 : $i]:
% 6.10/6.32         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 6.10/6.32          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 6.10/6.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.10/6.32  thf('129', plain,
% 6.10/6.32      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 6.10/6.32      inference('sup-', [status(thm)], ['127', '128'])).
% 6.10/6.32  thf('130', plain,
% 6.10/6.32      (![X2 : $i, X3 : $i]:
% 6.10/6.32         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 6.10/6.32           = (k3_xboole_0 @ X2 @ X3))),
% 6.10/6.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.10/6.32  thf('131', plain,
% 6.10/6.32      (![X0 : $i]:
% 6.10/6.32         ((k4_xboole_0 @ X0 @ (k3_subset_1 @ X0 @ X0))
% 6.10/6.32           = (k3_xboole_0 @ X0 @ X0))),
% 6.10/6.32      inference('sup+', [status(thm)], ['129', '130'])).
% 6.10/6.32  thf('132', plain,
% 6.10/6.32      (![X0 : $i]:
% 6.10/6.32         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0))
% 6.10/6.32           = (k3_xboole_0 @ X0 @ X0))),
% 6.10/6.32      inference('sup+', [status(thm)], ['126', '131'])).
% 6.10/6.32  thf('133', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 6.10/6.32      inference('sup+', [status(thm)], ['121', '132'])).
% 6.10/6.32  thf('134', plain,
% 6.10/6.32      (![X2 : $i, X3 : $i]:
% 6.10/6.32         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 6.10/6.32           = (k3_xboole_0 @ X2 @ X3))),
% 6.10/6.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.10/6.32  thf('135', plain,
% 6.10/6.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.32  thf('136', plain,
% 6.10/6.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.10/6.32         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 6.10/6.32          | (m1_subset_1 @ (k7_subset_1 @ X11 @ X10 @ X12) @ 
% 6.10/6.32             (k1_zfmisc_1 @ X11)))),
% 6.10/6.32      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 6.10/6.32  thf('137', plain,
% 6.10/6.32      (![X0 : $i]:
% 6.10/6.32         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 6.10/6.32          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.32      inference('sup-', [status(thm)], ['135', '136'])).
% 6.10/6.32  thf('138', plain,
% 6.10/6.32      (![X0 : $i]:
% 6.10/6.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 6.10/6.32           = (k4_xboole_0 @ sk_B @ X0))),
% 6.10/6.32      inference('sup-', [status(thm)], ['4', '5'])).
% 6.10/6.32  thf('139', plain,
% 6.10/6.32      (![X0 : $i]:
% 6.10/6.32         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 6.10/6.32          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.32      inference('demod', [status(thm)], ['137', '138'])).
% 6.10/6.32  thf('140', plain,
% 6.10/6.32      (![X0 : $i]:
% 6.10/6.32         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 6.10/6.32          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.32      inference('sup+', [status(thm)], ['134', '139'])).
% 6.10/6.32  thf('141', plain,
% 6.10/6.32      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 6.10/6.32         (~ (l1_pre_topc @ X35)
% 6.10/6.32          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 6.10/6.32          | ((k1_tops_1 @ X38 @ X37) != (X37))
% 6.10/6.32          | (v3_pre_topc @ X37 @ X38)
% 6.10/6.32          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.32          | ~ (l1_pre_topc @ X38)
% 6.10/6.32          | ~ (v2_pre_topc @ X38))),
% 6.10/6.32      inference('cnf', [status(esa)], [t55_tops_1])).
% 6.10/6.32  thf('142', plain,
% 6.10/6.32      ((![X37 : $i, X38 : $i]:
% 6.10/6.32          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.32           | ~ (l1_pre_topc @ X38)
% 6.10/6.32           | ~ (v2_pre_topc @ X38)
% 6.10/6.32           | ((k1_tops_1 @ X38 @ X37) != (X37))
% 6.10/6.32           | (v3_pre_topc @ X37 @ X38)))
% 6.10/6.32         <= ((![X37 : $i, X38 : $i]:
% 6.10/6.32                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.32                 | ~ (l1_pre_topc @ X38)
% 6.10/6.32                 | ~ (v2_pre_topc @ X38)
% 6.10/6.32                 | ((k1_tops_1 @ X38 @ X37) != (X37))
% 6.10/6.32                 | (v3_pre_topc @ X37 @ X38))))),
% 6.10/6.32      inference('split', [status(esa)], ['141'])).
% 6.10/6.32  thf('143', plain,
% 6.10/6.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.10/6.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.32  thf('144', plain,
% 6.10/6.32      ((![X35 : $i, X36 : $i]:
% 6.10/6.32          (~ (l1_pre_topc @ X35)
% 6.10/6.32           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))))
% 6.10/6.32         <= ((![X35 : $i, X36 : $i]:
% 6.10/6.32                (~ (l1_pre_topc @ X35)
% 6.10/6.32                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35))))))),
% 6.10/6.32      inference('split', [status(esa)], ['141'])).
% 6.10/6.32  thf('145', plain,
% 6.10/6.32      ((~ (l1_pre_topc @ sk_A))
% 6.10/6.32         <= ((![X35 : $i, X36 : $i]:
% 6.10/6.32                (~ (l1_pre_topc @ X35)
% 6.10/6.32                 | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35))))))),
% 6.10/6.32      inference('sup-', [status(thm)], ['143', '144'])).
% 6.10/6.32  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 6.10/6.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.32  thf('147', plain,
% 6.10/6.32      (~
% 6.10/6.32       (![X35 : $i, X36 : $i]:
% 6.10/6.32          (~ (l1_pre_topc @ X35)
% 6.10/6.32           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))))),
% 6.10/6.32      inference('demod', [status(thm)], ['145', '146'])).
% 6.10/6.32  thf('148', plain,
% 6.10/6.32      ((![X37 : $i, X38 : $i]:
% 6.10/6.32          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.32           | ~ (l1_pre_topc @ X38)
% 6.10/6.32           | ~ (v2_pre_topc @ X38)
% 6.10/6.32           | ((k1_tops_1 @ X38 @ X37) != (X37))
% 6.10/6.32           | (v3_pre_topc @ X37 @ X38))) | 
% 6.10/6.32       (![X35 : $i, X36 : $i]:
% 6.10/6.32          (~ (l1_pre_topc @ X35)
% 6.10/6.32           | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))))),
% 6.10/6.32      inference('split', [status(esa)], ['141'])).
% 6.10/6.32  thf('149', plain,
% 6.10/6.32      ((![X37 : $i, X38 : $i]:
% 6.10/6.32          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.32           | ~ (l1_pre_topc @ X38)
% 6.10/6.32           | ~ (v2_pre_topc @ X38)
% 6.10/6.32           | ((k1_tops_1 @ X38 @ X37) != (X37))
% 6.10/6.32           | (v3_pre_topc @ X37 @ X38)))),
% 6.10/6.32      inference('sat_resolution*', [status(thm)], ['147', '148'])).
% 6.10/6.32  thf('150', plain,
% 6.10/6.32      (![X37 : $i, X38 : $i]:
% 6.10/6.32         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.10/6.32          | ~ (l1_pre_topc @ X38)
% 6.10/6.32          | ~ (v2_pre_topc @ X38)
% 6.10/6.32          | ((k1_tops_1 @ X38 @ X37) != (X37))
% 6.10/6.32          | (v3_pre_topc @ X37 @ X38))),
% 6.10/6.32      inference('simpl_trail', [status(thm)], ['142', '149'])).
% 6.10/6.32  thf('151', plain,
% 6.10/6.32      (![X0 : $i]:
% 6.10/6.32         ((v3_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 6.10/6.32          | ((k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 6.10/6.32              != (k3_xboole_0 @ sk_B @ X0))
% 6.10/6.32          | ~ (v2_pre_topc @ sk_A)
% 6.10/6.32          | ~ (l1_pre_topc @ sk_A))),
% 6.10/6.32      inference('sup-', [status(thm)], ['140', '150'])).
% 6.10/6.32  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 6.10/6.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.32  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 6.10/6.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.10/6.32  thf('154', plain,
% 6.10/6.32      (![X0 : $i]:
% 6.10/6.32         ((v3_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 6.10/6.32          | ((k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 6.10/6.32              != (k3_xboole_0 @ sk_B @ X0)))),
% 6.10/6.32      inference('demod', [status(thm)], ['151', '152', '153'])).
% 6.10/6.32  thf('155', plain,
% 6.10/6.32      ((((k1_tops_1 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_B @ sk_B))
% 6.10/6.32        | (v3_pre_topc @ (k3_xboole_0 @ sk_B @ sk_B) @ sk_A))),
% 6.10/6.32      inference('sup-', [status(thm)], ['133', '154'])).
% 6.10/6.32  thf('156', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 6.10/6.32      inference('sup+', [status(thm)], ['121', '132'])).
% 6.10/6.32  thf('157', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 6.10/6.32      inference('sup+', [status(thm)], ['121', '132'])).
% 6.10/6.32  thf('158', plain,
% 6.10/6.32      ((((k1_tops_1 @ sk_A @ sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 6.10/6.32      inference('demod', [status(thm)], ['155', '156', '157'])).
% 6.10/6.32  thf('159', plain,
% 6.10/6.32      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 6.10/6.32      inference('split', [status(esa)], ['58'])).
% 6.10/6.32  thf('160', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 6.10/6.32      inference('sat_resolution*', [status(thm)], ['59', '93'])).
% 6.10/6.32  thf('161', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 6.10/6.32      inference('simpl_trail', [status(thm)], ['159', '160'])).
% 6.10/6.32  thf('162', plain, (((k1_tops_1 @ sk_A @ sk_B) != (sk_B))),
% 6.10/6.32      inference('clc', [status(thm)], ['158', '161'])).
% 6.10/6.32  thf('163', plain, ($false),
% 6.10/6.32      inference('simplify_reflect-', [status(thm)], ['118', '162'])).
% 6.10/6.32  
% 6.10/6.32  % SZS output end Refutation
% 6.10/6.32  
% 6.10/6.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
