%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8EGpxg7xDz

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:40 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 333 expanded)
%              Number of leaves         :   47 ( 118 expanded)
%              Depth                    :   17
%              Number of atoms          : 1576 (3741 expanded)
%              Number of equality atoms :  114 ( 242 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k1_tops_1 @ X64 @ X63 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k4_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k6_subset_1 @ X40 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k6_subset_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('24',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X62 @ X61 ) @ X61 )
      | ~ ( v4_pre_topc @ X61 @ X62 )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X34 @ ( k3_subset_1 @ X34 @ X33 ) )
        = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('32',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k6_subset_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('35',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('37',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','35','36'])).

thf('38',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['20','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k2_pre_topc @ X60 @ X59 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 @ ( k2_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['21'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('54',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('57',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('59',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('61',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('63',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('70',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('71',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('72',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['68','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','75'])).

thf(t49_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('77',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ ( k3_zfmisc_1 @ X50 @ X51 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('78',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('79',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('80',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('81',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('82',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      = X18 ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('86',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('91',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','89','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('97',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('98',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('99',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) )
      = X8 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','103'])).

thf('105',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('106',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('108',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k4_subset_1 @ X36 @ X35 @ X37 )
        = ( k2_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('109',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('110',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k4_subset_1 @ X36 @ X35 @ X37 )
        = ( k3_tarski @ ( k2_tarski @ X35 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) )
      = X8 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','114'])).

thf('116',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','115'])).

thf('117',plain,(
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

thf('118',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v2_pre_topc @ X54 )
      | ( ( k2_pre_topc @ X54 @ X53 )
       != X53 )
      | ( v4_pre_topc @ X53 @ X54 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['116','122'])).

thf('124',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('126',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','43','44','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8EGpxg7xDz
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:13:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.39/1.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.39/1.59  % Solved by: fo/fo7.sh
% 1.39/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.39/1.59  % done 3444 iterations in 1.135s
% 1.39/1.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.39/1.59  % SZS output start Refutation
% 1.39/1.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.39/1.59  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.39/1.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.39/1.59  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.39/1.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.39/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.39/1.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.39/1.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.39/1.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.39/1.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.39/1.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.39/1.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.39/1.59  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.39/1.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.39/1.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.39/1.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.39/1.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.39/1.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.39/1.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.39/1.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.39/1.59  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.39/1.59  thf(sk_B_type, type, sk_B: $i).
% 1.39/1.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.39/1.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.39/1.59  thf(t77_tops_1, conjecture,
% 1.39/1.59    (![A:$i]:
% 1.39/1.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.39/1.59       ( ![B:$i]:
% 1.39/1.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59           ( ( v4_pre_topc @ B @ A ) <=>
% 1.39/1.59             ( ( k2_tops_1 @ A @ B ) =
% 1.39/1.59               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.39/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.39/1.59    (~( ![A:$i]:
% 1.39/1.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.39/1.59          ( ![B:$i]:
% 1.39/1.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59              ( ( v4_pre_topc @ B @ A ) <=>
% 1.39/1.59                ( ( k2_tops_1 @ A @ B ) =
% 1.39/1.59                  ( k7_subset_1 @
% 1.39/1.59                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.39/1.59    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.39/1.59  thf('0', plain,
% 1.39/1.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59              (k1_tops_1 @ sk_A @ sk_B)))
% 1.39/1.59        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('1', plain,
% 1.39/1.59      (~
% 1.39/1.59       (((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.39/1.59       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.39/1.59      inference('split', [status(esa)], ['0'])).
% 1.39/1.59  thf('2', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(t74_tops_1, axiom,
% 1.39/1.59    (![A:$i]:
% 1.39/1.59     ( ( l1_pre_topc @ A ) =>
% 1.39/1.59       ( ![B:$i]:
% 1.39/1.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59           ( ( k1_tops_1 @ A @ B ) =
% 1.39/1.59             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.39/1.59  thf('3', plain,
% 1.39/1.59      (![X63 : $i, X64 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 1.39/1.59          | ((k1_tops_1 @ X64 @ X63)
% 1.39/1.59              = (k7_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 1.39/1.59                 (k2_tops_1 @ X64 @ X63)))
% 1.39/1.59          | ~ (l1_pre_topc @ X64))),
% 1.39/1.59      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.39/1.59  thf('4', plain,
% 1.39/1.59      ((~ (l1_pre_topc @ sk_A)
% 1.39/1.59        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.39/1.59            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.39/1.59      inference('sup-', [status(thm)], ['2', '3'])).
% 1.39/1.59  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('6', plain,
% 1.39/1.59      (((k1_tops_1 @ sk_A @ sk_B)
% 1.39/1.59         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.39/1.59      inference('demod', [status(thm)], ['4', '5'])).
% 1.39/1.59  thf('7', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(redefinition_k7_subset_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.39/1.59       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.39/1.59  thf('8', plain,
% 1.39/1.59      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 1.39/1.59          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k4_xboole_0 @ X40 @ X42)))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.39/1.59  thf(redefinition_k6_subset_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.39/1.59  thf('9', plain,
% 1.39/1.59      (![X38 : $i, X39 : $i]:
% 1.39/1.59         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.39/1.59  thf('10', plain,
% 1.39/1.59      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 1.39/1.59          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k6_subset_1 @ X40 @ X42)))),
% 1.39/1.59      inference('demod', [status(thm)], ['8', '9'])).
% 1.39/1.59  thf('11', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.39/1.59           = (k6_subset_1 @ sk_B @ X0))),
% 1.39/1.59      inference('sup-', [status(thm)], ['7', '10'])).
% 1.39/1.59  thf('12', plain,
% 1.39/1.59      (((k1_tops_1 @ sk_A @ sk_B)
% 1.39/1.59         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.39/1.59      inference('demod', [status(thm)], ['6', '11'])).
% 1.39/1.59  thf(dt_k6_subset_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.39/1.59  thf('13', plain,
% 1.39/1.59      (![X31 : $i, X32 : $i]:
% 1.39/1.59         (m1_subset_1 @ (k6_subset_1 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))),
% 1.39/1.59      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.39/1.59  thf(d5_subset_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.39/1.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.39/1.59  thf('14', plain,
% 1.39/1.59      (![X27 : $i, X28 : $i]:
% 1.39/1.59         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 1.39/1.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.39/1.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.39/1.59  thf('15', plain,
% 1.39/1.59      (![X38 : $i, X39 : $i]:
% 1.39/1.59         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.39/1.59  thf('16', plain,
% 1.39/1.59      (![X27 : $i, X28 : $i]:
% 1.39/1.59         (((k3_subset_1 @ X27 @ X28) = (k6_subset_1 @ X27 @ X28))
% 1.39/1.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.39/1.59      inference('demod', [status(thm)], ['14', '15'])).
% 1.39/1.59  thf('17', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.39/1.59           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['13', '16'])).
% 1.39/1.59  thf('18', plain,
% 1.39/1.59      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.39/1.59         = (k6_subset_1 @ sk_B @ 
% 1.39/1.59            (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.39/1.59      inference('sup+', [status(thm)], ['12', '17'])).
% 1.39/1.59  thf('19', plain,
% 1.39/1.59      (((k1_tops_1 @ sk_A @ sk_B)
% 1.39/1.59         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.39/1.59      inference('demod', [status(thm)], ['6', '11'])).
% 1.39/1.59  thf('20', plain,
% 1.39/1.59      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.39/1.59         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.39/1.59      inference('demod', [status(thm)], ['18', '19'])).
% 1.39/1.59  thf('21', plain,
% 1.39/1.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59             (k1_tops_1 @ sk_A @ sk_B)))
% 1.39/1.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('22', plain,
% 1.39/1.59      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('split', [status(esa)], ['21'])).
% 1.39/1.59  thf('23', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(t69_tops_1, axiom,
% 1.39/1.59    (![A:$i]:
% 1.39/1.59     ( ( l1_pre_topc @ A ) =>
% 1.39/1.59       ( ![B:$i]:
% 1.39/1.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59           ( ( v4_pre_topc @ B @ A ) =>
% 1.39/1.59             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.39/1.59  thf('24', plain,
% 1.39/1.59      (![X61 : $i, X62 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 1.39/1.59          | (r1_tarski @ (k2_tops_1 @ X62 @ X61) @ X61)
% 1.39/1.59          | ~ (v4_pre_topc @ X61 @ X62)
% 1.39/1.59          | ~ (l1_pre_topc @ X62))),
% 1.39/1.59      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.39/1.59  thf('25', plain,
% 1.39/1.59      ((~ (l1_pre_topc @ sk_A)
% 1.39/1.59        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.39/1.59        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.39/1.59      inference('sup-', [status(thm)], ['23', '24'])).
% 1.39/1.59  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('27', plain,
% 1.39/1.59      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.39/1.59        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.39/1.59      inference('demod', [status(thm)], ['25', '26'])).
% 1.39/1.59  thf('28', plain,
% 1.39/1.59      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.39/1.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['22', '27'])).
% 1.39/1.59  thf(t3_subset, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.39/1.59  thf('29', plain,
% 1.39/1.59      (![X47 : $i, X49 : $i]:
% 1.39/1.59         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 1.39/1.59      inference('cnf', [status(esa)], [t3_subset])).
% 1.39/1.59  thf('30', plain,
% 1.39/1.59      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.39/1.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['28', '29'])).
% 1.39/1.59  thf(involutiveness_k3_subset_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.39/1.59       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.39/1.59  thf('31', plain,
% 1.39/1.59      (![X33 : $i, X34 : $i]:
% 1.39/1.59         (((k3_subset_1 @ X34 @ (k3_subset_1 @ X34 @ X33)) = (X33))
% 1.39/1.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 1.39/1.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.39/1.59  thf('32', plain,
% 1.39/1.59      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.39/1.59          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.39/1.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['30', '31'])).
% 1.39/1.59  thf('33', plain,
% 1.39/1.59      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.39/1.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['28', '29'])).
% 1.39/1.59  thf('34', plain,
% 1.39/1.59      (![X27 : $i, X28 : $i]:
% 1.39/1.59         (((k3_subset_1 @ X27 @ X28) = (k6_subset_1 @ X27 @ X28))
% 1.39/1.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.39/1.59      inference('demod', [status(thm)], ['14', '15'])).
% 1.39/1.59  thf('35', plain,
% 1.39/1.59      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.39/1.59          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.39/1.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['33', '34'])).
% 1.39/1.59  thf('36', plain,
% 1.39/1.59      (((k1_tops_1 @ sk_A @ sk_B)
% 1.39/1.59         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.39/1.59      inference('demod', [status(thm)], ['6', '11'])).
% 1.39/1.59  thf('37', plain,
% 1.39/1.59      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.39/1.59          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.39/1.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('demod', [status(thm)], ['32', '35', '36'])).
% 1.39/1.59  thf('38', plain,
% 1.39/1.59      ((((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.39/1.59          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.39/1.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('sup+', [status(thm)], ['20', '37'])).
% 1.39/1.59  thf('39', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.39/1.59           = (k6_subset_1 @ sk_B @ X0))),
% 1.39/1.59      inference('sup-', [status(thm)], ['7', '10'])).
% 1.39/1.59  thf('40', plain,
% 1.39/1.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59              (k1_tops_1 @ sk_A @ sk_B))))
% 1.39/1.59         <= (~
% 1.39/1.59             (((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('split', [status(esa)], ['0'])).
% 1.39/1.59  thf('41', plain,
% 1.39/1.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.39/1.59         <= (~
% 1.39/1.59             (((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup-', [status(thm)], ['39', '40'])).
% 1.39/1.59  thf('42', plain,
% 1.39/1.59      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.39/1.59         <= (~
% 1.39/1.59             (((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.39/1.59             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['38', '41'])).
% 1.39/1.59  thf('43', plain,
% 1.39/1.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.39/1.59       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.39/1.59      inference('simplify', [status(thm)], ['42'])).
% 1.39/1.59  thf('44', plain,
% 1.39/1.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.39/1.59       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.39/1.59      inference('split', [status(esa)], ['21'])).
% 1.39/1.59  thf('45', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(t65_tops_1, axiom,
% 1.39/1.59    (![A:$i]:
% 1.39/1.59     ( ( l1_pre_topc @ A ) =>
% 1.39/1.59       ( ![B:$i]:
% 1.39/1.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59           ( ( k2_pre_topc @ A @ B ) =
% 1.39/1.59             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.39/1.59  thf('46', plain,
% 1.39/1.59      (![X59 : $i, X60 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 1.39/1.59          | ((k2_pre_topc @ X60 @ X59)
% 1.39/1.59              = (k4_subset_1 @ (u1_struct_0 @ X60) @ X59 @ 
% 1.39/1.59                 (k2_tops_1 @ X60 @ X59)))
% 1.39/1.59          | ~ (l1_pre_topc @ X60))),
% 1.39/1.59      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.39/1.59  thf('47', plain,
% 1.39/1.59      ((~ (l1_pre_topc @ sk_A)
% 1.39/1.59        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.39/1.59            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.39/1.59      inference('sup-', [status(thm)], ['45', '46'])).
% 1.39/1.59  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('49', plain,
% 1.39/1.59      (((k2_pre_topc @ sk_A @ sk_B)
% 1.39/1.59         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.39/1.59      inference('demod', [status(thm)], ['47', '48'])).
% 1.39/1.59  thf('50', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.39/1.59           = (k6_subset_1 @ sk_B @ X0))),
% 1.39/1.59      inference('sup-', [status(thm)], ['7', '10'])).
% 1.39/1.59  thf('51', plain,
% 1.39/1.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59             (k1_tops_1 @ sk_A @ sk_B))))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('split', [status(esa)], ['21'])).
% 1.39/1.59  thf('52', plain,
% 1.39/1.59      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup+', [status(thm)], ['50', '51'])).
% 1.39/1.59  thf(t36_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.39/1.59  thf('53', plain,
% 1.39/1.59      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 1.39/1.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.39/1.59  thf('54', plain,
% 1.39/1.59      (![X38 : $i, X39 : $i]:
% 1.39/1.59         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.39/1.59  thf('55', plain,
% 1.39/1.59      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 1.39/1.59      inference('demod', [status(thm)], ['53', '54'])).
% 1.39/1.59  thf('56', plain,
% 1.39/1.59      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup+', [status(thm)], ['52', '55'])).
% 1.39/1.59  thf(t1_boole, axiom,
% 1.39/1.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.39/1.59  thf('57', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.39/1.59      inference('cnf', [status(esa)], [t1_boole])).
% 1.39/1.59  thf(l51_zfmisc_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.39/1.59  thf('58', plain,
% 1.39/1.59      (![X24 : $i, X25 : $i]:
% 1.39/1.59         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.39/1.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.39/1.59  thf('59', plain,
% 1.39/1.59      (![X4 : $i]: ((k3_tarski @ (k2_tarski @ X4 @ k1_xboole_0)) = (X4))),
% 1.39/1.59      inference('demod', [status(thm)], ['57', '58'])).
% 1.39/1.59  thf(t43_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.39/1.59       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.39/1.59  thf('60', plain,
% 1.39/1.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.39/1.59         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.39/1.59          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.39/1.59      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.39/1.59  thf('61', plain,
% 1.39/1.59      (![X38 : $i, X39 : $i]:
% 1.39/1.59         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.39/1.59  thf('62', plain,
% 1.39/1.59      (![X24 : $i, X25 : $i]:
% 1.39/1.59         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.39/1.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.39/1.59  thf('63', plain,
% 1.39/1.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.39/1.59         ((r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X14)
% 1.39/1.59          | ~ (r1_tarski @ X12 @ (k3_tarski @ (k2_tarski @ X13 @ X14))))),
% 1.39/1.59      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.39/1.59  thf('64', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (~ (r1_tarski @ X1 @ X0)
% 1.39/1.59          | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ k1_xboole_0))),
% 1.39/1.59      inference('sup-', [status(thm)], ['59', '63'])).
% 1.39/1.59  thf('65', plain,
% 1.39/1.59      (((r1_tarski @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.39/1.59         k1_xboole_0))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup-', [status(thm)], ['56', '64'])).
% 1.39/1.59  thf(t1_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.39/1.59       ( r1_tarski @ A @ C ) ))).
% 1.39/1.59  thf('66', plain,
% 1.39/1.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.39/1.59         (~ (r1_tarski @ X5 @ X6)
% 1.39/1.59          | ~ (r1_tarski @ X6 @ X7)
% 1.39/1.59          | (r1_tarski @ X5 @ X7))),
% 1.39/1.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.39/1.59  thf('67', plain,
% 1.39/1.59      ((![X0 : $i]:
% 1.39/1.59          ((r1_tarski @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0)
% 1.39/1.59           | ~ (r1_tarski @ k1_xboole_0 @ X0)))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup-', [status(thm)], ['65', '66'])).
% 1.39/1.59  thf('68', plain,
% 1.39/1.59      (![X4 : $i]: ((k3_tarski @ (k2_tarski @ X4 @ k1_xboole_0)) = (X4))),
% 1.39/1.59      inference('demod', [status(thm)], ['57', '58'])).
% 1.39/1.59  thf('69', plain,
% 1.39/1.59      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 1.39/1.59      inference('demod', [status(thm)], ['53', '54'])).
% 1.39/1.59  thf(t44_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.39/1.59       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.39/1.59  thf('70', plain,
% 1.39/1.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.39/1.59         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.39/1.59          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 1.39/1.59      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.39/1.59  thf('71', plain,
% 1.39/1.59      (![X24 : $i, X25 : $i]:
% 1.39/1.59         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.39/1.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.39/1.59  thf('72', plain,
% 1.39/1.59      (![X38 : $i, X39 : $i]:
% 1.39/1.59         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.39/1.59  thf('73', plain,
% 1.39/1.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.39/1.59         ((r1_tarski @ X15 @ (k3_tarski @ (k2_tarski @ X16 @ X17)))
% 1.39/1.59          | ~ (r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17))),
% 1.39/1.59      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.39/1.59  thf('74', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['69', '73'])).
% 1.39/1.59  thf('75', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.39/1.59      inference('sup+', [status(thm)], ['68', '74'])).
% 1.39/1.59  thf('76', plain,
% 1.39/1.59      ((![X0 : $i]:
% 1.39/1.59          (r1_tarski @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('demod', [status(thm)], ['67', '75'])).
% 1.39/1.59  thf(t49_mcart_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( ~( ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) & 
% 1.39/1.59            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) ) ) & 
% 1.39/1.59            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) ) ) ) =>
% 1.39/1.59       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.39/1.59  thf('77', plain,
% 1.39/1.59      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.39/1.59         (((X50) = (k1_xboole_0))
% 1.39/1.59          | ~ (r1_tarski @ X50 @ (k3_zfmisc_1 @ X50 @ X51 @ X52)))),
% 1.39/1.59      inference('cnf', [status(esa)], [t49_mcart_1])).
% 1.39/1.59  thf('78', plain,
% 1.39/1.59      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup-', [status(thm)], ['76', '77'])).
% 1.39/1.59  thf(t51_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.39/1.59       ( A ) ))).
% 1.39/1.59  thf('79', plain,
% 1.39/1.59      (![X18 : $i, X19 : $i]:
% 1.39/1.59         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 1.39/1.59           = (X18))),
% 1.39/1.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.39/1.59  thf('80', plain,
% 1.39/1.59      (![X38 : $i, X39 : $i]:
% 1.39/1.59         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.39/1.59  thf('81', plain,
% 1.39/1.59      (![X24 : $i, X25 : $i]:
% 1.39/1.59         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.39/1.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.39/1.59  thf(commutativity_k2_tarski, axiom,
% 1.39/1.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.39/1.59  thf('82', plain,
% 1.39/1.59      (![X22 : $i, X23 : $i]:
% 1.39/1.59         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.39/1.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.39/1.59  thf('83', plain,
% 1.39/1.59      (![X18 : $i, X19 : $i]:
% 1.39/1.59         ((k3_tarski @ 
% 1.39/1.59           (k2_tarski @ (k6_subset_1 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X19)))
% 1.39/1.59           = (X18))),
% 1.39/1.59      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 1.39/1.59  thf('84', plain,
% 1.39/1.59      ((((k3_tarski @ 
% 1.39/1.59          (k2_tarski @ k1_xboole_0 @ 
% 1.39/1.59           (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.39/1.59          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup+', [status(thm)], ['78', '83'])).
% 1.39/1.59  thf('85', plain,
% 1.39/1.59      (![X22 : $i, X23 : $i]:
% 1.39/1.59         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.39/1.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.39/1.59  thf(t12_setfam_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.39/1.59  thf('86', plain,
% 1.39/1.59      (![X45 : $i, X46 : $i]:
% 1.39/1.59         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 1.39/1.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.39/1.59  thf('87', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.39/1.59      inference('sup+', [status(thm)], ['85', '86'])).
% 1.39/1.59  thf('88', plain,
% 1.39/1.59      (![X45 : $i, X46 : $i]:
% 1.39/1.59         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 1.39/1.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.39/1.59  thf('89', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.39/1.59      inference('sup+', [status(thm)], ['87', '88'])).
% 1.39/1.59  thf('90', plain,
% 1.39/1.59      (![X22 : $i, X23 : $i]:
% 1.39/1.59         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.39/1.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.39/1.59  thf('91', plain,
% 1.39/1.59      (![X4 : $i]: ((k3_tarski @ (k2_tarski @ X4 @ k1_xboole_0)) = (X4))),
% 1.39/1.59      inference('demod', [status(thm)], ['57', '58'])).
% 1.39/1.59  thf('92', plain,
% 1.39/1.59      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 1.39/1.59      inference('sup+', [status(thm)], ['90', '91'])).
% 1.39/1.59  thf('93', plain,
% 1.39/1.59      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.39/1.59          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('demod', [status(thm)], ['84', '89', '92'])).
% 1.39/1.59  thf('94', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('95', plain,
% 1.39/1.59      (![X47 : $i, X48 : $i]:
% 1.39/1.59         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 1.39/1.59      inference('cnf', [status(esa)], [t3_subset])).
% 1.39/1.59  thf('96', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.39/1.59      inference('sup-', [status(thm)], ['94', '95'])).
% 1.39/1.59  thf(t22_xboole_1, axiom,
% 1.39/1.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.39/1.59  thf('97', plain,
% 1.39/1.59      (![X8 : $i, X9 : $i]:
% 1.39/1.59         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 1.39/1.59      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.39/1.59  thf('98', plain,
% 1.39/1.59      (![X24 : $i, X25 : $i]:
% 1.39/1.59         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.39/1.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.39/1.59  thf('99', plain,
% 1.39/1.59      (![X8 : $i, X9 : $i]:
% 1.39/1.59         ((k3_tarski @ (k2_tarski @ X8 @ (k3_xboole_0 @ X8 @ X9))) = (X8))),
% 1.39/1.59      inference('demod', [status(thm)], ['97', '98'])).
% 1.39/1.59  thf('100', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['69', '73'])).
% 1.39/1.59  thf('101', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.39/1.59      inference('sup+', [status(thm)], ['99', '100'])).
% 1.39/1.59  thf('102', plain,
% 1.39/1.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.39/1.59         (~ (r1_tarski @ X5 @ X6)
% 1.39/1.59          | ~ (r1_tarski @ X6 @ X7)
% 1.39/1.59          | (r1_tarski @ X5 @ X7))),
% 1.39/1.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.39/1.59  thf('103', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.59         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.39/1.59      inference('sup-', [status(thm)], ['101', '102'])).
% 1.39/1.59  thf('104', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.39/1.59      inference('sup-', [status(thm)], ['96', '103'])).
% 1.39/1.59  thf('105', plain,
% 1.39/1.59      (![X47 : $i, X49 : $i]:
% 1.39/1.59         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 1.39/1.59      inference('cnf', [status(esa)], [t3_subset])).
% 1.39/1.59  thf('106', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 1.39/1.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['104', '105'])).
% 1.39/1.59  thf('107', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(redefinition_k4_subset_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.39/1.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.39/1.59       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.39/1.59  thf('108', plain,
% 1.39/1.59      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.39/1.59          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 1.39/1.59          | ((k4_subset_1 @ X36 @ X35 @ X37) = (k2_xboole_0 @ X35 @ X37)))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.39/1.59  thf('109', plain,
% 1.39/1.59      (![X24 : $i, X25 : $i]:
% 1.39/1.59         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.39/1.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.39/1.59  thf('110', plain,
% 1.39/1.59      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.39/1.59          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 1.39/1.59          | ((k4_subset_1 @ X36 @ X35 @ X37)
% 1.39/1.59              = (k3_tarski @ (k2_tarski @ X35 @ X37))))),
% 1.39/1.59      inference('demod', [status(thm)], ['108', '109'])).
% 1.39/1.59  thf('111', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.39/1.59            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 1.39/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.39/1.59      inference('sup-', [status(thm)], ['107', '110'])).
% 1.39/1.59  thf('112', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59           (k3_xboole_0 @ sk_B @ X0))
% 1.39/1.59           = (k3_tarski @ (k2_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ X0))))),
% 1.39/1.59      inference('sup-', [status(thm)], ['106', '111'])).
% 1.39/1.59  thf('113', plain,
% 1.39/1.59      (![X8 : $i, X9 : $i]:
% 1.39/1.59         ((k3_tarski @ (k2_tarski @ X8 @ (k3_xboole_0 @ X8 @ X9))) = (X8))),
% 1.39/1.59      inference('demod', [status(thm)], ['97', '98'])).
% 1.39/1.59  thf('114', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59           (k3_xboole_0 @ sk_B @ X0)) = (sk_B))),
% 1.39/1.59      inference('demod', [status(thm)], ['112', '113'])).
% 1.39/1.59  thf('115', plain,
% 1.39/1.59      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.39/1.59          = (sk_B)))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup+', [status(thm)], ['93', '114'])).
% 1.39/1.59  thf('116', plain,
% 1.39/1.59      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup+', [status(thm)], ['49', '115'])).
% 1.39/1.59  thf('117', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(t52_pre_topc, axiom,
% 1.39/1.59    (![A:$i]:
% 1.39/1.59     ( ( l1_pre_topc @ A ) =>
% 1.39/1.59       ( ![B:$i]:
% 1.39/1.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.39/1.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.39/1.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.39/1.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.39/1.59  thf('118', plain,
% 1.39/1.59      (![X53 : $i, X54 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.39/1.59          | ~ (v2_pre_topc @ X54)
% 1.39/1.59          | ((k2_pre_topc @ X54 @ X53) != (X53))
% 1.39/1.59          | (v4_pre_topc @ X53 @ X54)
% 1.39/1.59          | ~ (l1_pre_topc @ X54))),
% 1.39/1.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.39/1.59  thf('119', plain,
% 1.39/1.59      ((~ (l1_pre_topc @ sk_A)
% 1.39/1.59        | (v4_pre_topc @ sk_B @ sk_A)
% 1.39/1.59        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.39/1.59        | ~ (v2_pre_topc @ sk_A))),
% 1.39/1.59      inference('sup-', [status(thm)], ['117', '118'])).
% 1.39/1.59  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('122', plain,
% 1.39/1.59      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.39/1.59      inference('demod', [status(thm)], ['119', '120', '121'])).
% 1.39/1.59  thf('123', plain,
% 1.39/1.59      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('sup-', [status(thm)], ['116', '122'])).
% 1.39/1.59  thf('124', plain,
% 1.39/1.59      (((v4_pre_topc @ sk_B @ sk_A))
% 1.39/1.59         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.39/1.59      inference('simplify', [status(thm)], ['123'])).
% 1.39/1.59  thf('125', plain,
% 1.39/1.59      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.39/1.59      inference('split', [status(esa)], ['0'])).
% 1.39/1.59  thf('126', plain,
% 1.39/1.59      (~
% 1.39/1.59       (((k2_tops_1 @ sk_A @ sk_B)
% 1.39/1.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.39/1.59             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.39/1.59       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.39/1.59      inference('sup-', [status(thm)], ['124', '125'])).
% 1.39/1.59  thf('127', plain, ($false),
% 1.39/1.59      inference('sat_resolution*', [status(thm)], ['1', '43', '44', '126'])).
% 1.39/1.59  
% 1.39/1.59  % SZS output end Refutation
% 1.39/1.59  
% 1.39/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
