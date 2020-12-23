%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Txe7gf6CLT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:37 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 264 expanded)
%              Number of leaves         :   38 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          : 1384 (3152 expanded)
%              Number of equality atoms :   89 ( 178 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('3',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X55 @ X54 ) @ X54 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k6_subset_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('16',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X61 @ X60 ) @ X60 )
      | ~ ( v4_pre_topc @ X60 @ X61 )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X34 @ ( k3_subset_1 @ X34 @ X33 ) )
        = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('24',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k6_subset_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('27',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( ( k1_tops_1 @ X63 @ X62 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X63 ) @ X62 @ ( k2_tops_1 @ X63 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k4_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('34',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('35',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k6_subset_1 @ X40 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','36'])).

thf('38',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','37'])).

thf('39',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','38'])).

thf('40',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['12','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k2_pre_topc @ X59 @ X58 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 @ ( k2_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('58',plain,(
    ! [X31: $i,X32: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('59',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('62',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['67','78'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('80',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k4_subset_1 @ X36 @ X35 @ X37 )
        = ( k2_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('81',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('82',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k4_subset_1 @ X36 @ X35 @ X37 )
        = ( k3_tarski @ ( k2_tarski @ X35 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B @ X1 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( k4_subset_1 @ ( k3_tarski @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','83'])).

thf('85',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('86',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('89',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('91',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('92',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('93',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X6 @ X5 ) )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('96',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','89','96'])).

thf('98',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','97'])).

thf('99',plain,(
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

thf('100',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v2_pre_topc @ X51 )
      | ( ( k2_pre_topc @ X51 @ X50 )
       != X50 )
      | ( v4_pre_topc @ X50 @ X51 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','45','46','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Txe7gf6CLT
% 0.13/0.36  % Computer   : n021.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:11:50 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.90/1.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.09  % Solved by: fo/fo7.sh
% 0.90/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.09  % done 2057 iterations in 0.616s
% 0.90/1.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.09  % SZS output start Refutation
% 0.90/1.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.09  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.90/1.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.09  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.90/1.09  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.90/1.09  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.90/1.09  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.09  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.90/1.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.09  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.90/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.09  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.09  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.90/1.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.09  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.90/1.09  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.90/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.09  thf(t77_tops_1, conjecture,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( ( v4_pre_topc @ B @ A ) <=>
% 0.90/1.09             ( ( k2_tops_1 @ A @ B ) =
% 0.90/1.09               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.09    (~( ![A:$i]:
% 0.90/1.09        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.09          ( ![B:$i]:
% 0.90/1.09            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09              ( ( v4_pre_topc @ B @ A ) <=>
% 0.90/1.09                ( ( k2_tops_1 @ A @ B ) =
% 0.90/1.09                  ( k7_subset_1 @
% 0.90/1.09                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.90/1.09    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.90/1.09  thf('0', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09              (k1_tops_1 @ sk_A @ sk_B)))
% 0.90/1.09        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('1', plain,
% 0.90/1.09      (~
% 0.90/1.09       (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.90/1.09       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('split', [status(esa)], ['0'])).
% 0.90/1.09  thf('2', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t44_tops_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( l1_pre_topc @ A ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.90/1.09  thf('3', plain,
% 0.90/1.09      (![X54 : $i, X55 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 0.90/1.09          | (r1_tarski @ (k1_tops_1 @ X55 @ X54) @ X54)
% 0.90/1.09          | ~ (l1_pre_topc @ X55))),
% 0.90/1.09      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.90/1.09  thf('4', plain,
% 0.90/1.09      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.09  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('6', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.90/1.09      inference('demod', [status(thm)], ['4', '5'])).
% 0.90/1.09  thf(t3_subset, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.09  thf('7', plain,
% 0.90/1.09      (![X47 : $i, X49 : $i]:
% 0.90/1.09         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.09  thf('8', plain,
% 0.90/1.09      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.09  thf(d5_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.90/1.09  thf('9', plain,
% 0.90/1.09      (![X27 : $i, X28 : $i]:
% 0.90/1.09         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.90/1.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.90/1.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.90/1.09  thf(redefinition_k6_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.90/1.09  thf('10', plain,
% 0.90/1.09      (![X38 : $i, X39 : $i]:
% 0.90/1.09         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.09  thf('11', plain,
% 0.90/1.09      (![X27 : $i, X28 : $i]:
% 0.90/1.09         (((k3_subset_1 @ X27 @ X28) = (k6_subset_1 @ X27 @ X28))
% 0.90/1.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.90/1.09      inference('demod', [status(thm)], ['9', '10'])).
% 0.90/1.09  thf('12', plain,
% 0.90/1.09      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.90/1.09         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['8', '11'])).
% 0.90/1.09  thf('13', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09             (k1_tops_1 @ sk_A @ sk_B)))
% 0.90/1.09        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('14', plain,
% 0.90/1.09      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('split', [status(esa)], ['13'])).
% 0.90/1.09  thf('15', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t69_tops_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( l1_pre_topc @ A ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( ( v4_pre_topc @ B @ A ) =>
% 0.90/1.09             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.90/1.09  thf('16', plain,
% 0.90/1.09      (![X60 : $i, X61 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 0.90/1.09          | (r1_tarski @ (k2_tops_1 @ X61 @ X60) @ X60)
% 0.90/1.09          | ~ (v4_pre_topc @ X60 @ X61)
% 0.90/1.09          | ~ (l1_pre_topc @ X61))),
% 0.90/1.09      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.90/1.09  thf('17', plain,
% 0.90/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.09        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.90/1.09        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['15', '16'])).
% 0.90/1.09  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('19', plain,
% 0.90/1.09      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.90/1.09        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['17', '18'])).
% 0.90/1.09  thf('20', plain,
% 0.90/1.09      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.90/1.09         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['14', '19'])).
% 0.90/1.09  thf('21', plain,
% 0.90/1.09      (![X47 : $i, X49 : $i]:
% 0.90/1.09         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.09  thf('22', plain,
% 0.90/1.09      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.90/1.09         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.09  thf(involutiveness_k3_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.90/1.09  thf('23', plain,
% 0.90/1.09      (![X33 : $i, X34 : $i]:
% 0.90/1.09         (((k3_subset_1 @ X34 @ (k3_subset_1 @ X34 @ X33)) = (X33))
% 0.90/1.09          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.90/1.09      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.90/1.09  thf('24', plain,
% 0.90/1.09      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.90/1.09          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.90/1.09         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.09  thf('25', plain,
% 0.90/1.09      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.90/1.09         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.09  thf('26', plain,
% 0.90/1.09      (![X27 : $i, X28 : $i]:
% 0.90/1.09         (((k3_subset_1 @ X27 @ X28) = (k6_subset_1 @ X27 @ X28))
% 0.90/1.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.90/1.09      inference('demod', [status(thm)], ['9', '10'])).
% 0.90/1.09  thf('27', plain,
% 0.90/1.09      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.90/1.09         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['25', '26'])).
% 0.90/1.09  thf('28', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t74_tops_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( l1_pre_topc @ A ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( ( k1_tops_1 @ A @ B ) =
% 0.90/1.09             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.09  thf('29', plain,
% 0.90/1.09      (![X62 : $i, X63 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 0.90/1.09          | ((k1_tops_1 @ X63 @ X62)
% 0.90/1.09              = (k7_subset_1 @ (u1_struct_0 @ X63) @ X62 @ 
% 0.90/1.09                 (k2_tops_1 @ X63 @ X62)))
% 0.90/1.09          | ~ (l1_pre_topc @ X63))),
% 0.90/1.09      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.90/1.09  thf('30', plain,
% 0.90/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.09        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.90/1.09            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.09  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('32', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(redefinition_k7_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.90/1.09  thf('33', plain,
% 0.90/1.09      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.90/1.09          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k4_xboole_0 @ X40 @ X42)))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.90/1.09  thf('34', plain,
% 0.90/1.09      (![X38 : $i, X39 : $i]:
% 0.90/1.09         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.09  thf('35', plain,
% 0.90/1.09      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.90/1.09          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k6_subset_1 @ X40 @ X42)))),
% 0.90/1.09      inference('demod', [status(thm)], ['33', '34'])).
% 0.90/1.09  thf('36', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.90/1.09           = (k6_subset_1 @ sk_B @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['32', '35'])).
% 0.90/1.09  thf('37', plain,
% 0.90/1.09      (((k1_tops_1 @ sk_A @ sk_B)
% 0.90/1.09         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['30', '31', '36'])).
% 0.90/1.09  thf('38', plain,
% 0.90/1.09      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.90/1.09         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['27', '37'])).
% 0.90/1.09  thf('39', plain,
% 0.90/1.09      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.90/1.09         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['24', '38'])).
% 0.90/1.09  thf('40', plain,
% 0.90/1.09      ((((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.90/1.09         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup+', [status(thm)], ['12', '39'])).
% 0.90/1.09  thf('41', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.90/1.09           = (k6_subset_1 @ sk_B @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['32', '35'])).
% 0.90/1.09  thf('42', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09              (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.09         <= (~
% 0.90/1.09             (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('split', [status(esa)], ['0'])).
% 0.90/1.09  thf('43', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.09         <= (~
% 0.90/1.09             (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['41', '42'])).
% 0.90/1.09  thf('44', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.90/1.09         <= (~
% 0.90/1.09             (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.90/1.09             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['40', '43'])).
% 0.90/1.09  thf('45', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.90/1.09       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('simplify', [status(thm)], ['44'])).
% 0.90/1.09  thf('46', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.90/1.09       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('split', [status(esa)], ['13'])).
% 0.90/1.09  thf('47', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t65_tops_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( l1_pre_topc @ A ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( ( k2_pre_topc @ A @ B ) =
% 0.90/1.09             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.09  thf('48', plain,
% 0.90/1.09      (![X58 : $i, X59 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 0.90/1.09          | ((k2_pre_topc @ X59 @ X58)
% 0.90/1.09              = (k4_subset_1 @ (u1_struct_0 @ X59) @ X58 @ 
% 0.90/1.09                 (k2_tops_1 @ X59 @ X58)))
% 0.90/1.09          | ~ (l1_pre_topc @ X59))),
% 0.90/1.09      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.90/1.09  thf('49', plain,
% 0.90/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.09        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.90/1.09            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.09  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('51', plain,
% 0.90/1.09      (((k2_pre_topc @ sk_A @ sk_B)
% 0.90/1.09         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['49', '50'])).
% 0.90/1.09  thf(t7_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.09  thf('52', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.90/1.09      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.09  thf(l51_zfmisc_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.09  thf('53', plain,
% 0.90/1.09      (![X24 : $i, X25 : $i]:
% 0.90/1.09         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 0.90/1.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.90/1.09  thf('54', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i]:
% 0.90/1.09         (r1_tarski @ X18 @ (k3_tarski @ (k2_tarski @ X18 @ X19)))),
% 0.90/1.09      inference('demod', [status(thm)], ['52', '53'])).
% 0.90/1.09  thf('55', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.90/1.09           = (k6_subset_1 @ sk_B @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['32', '35'])).
% 0.90/1.09  thf('56', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09             (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('split', [status(esa)], ['13'])).
% 0.90/1.09  thf('57', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['55', '56'])).
% 0.90/1.09  thf(dt_k6_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.09  thf('58', plain,
% 0.90/1.09      (![X31 : $i, X32 : $i]:
% 0.90/1.09         (m1_subset_1 @ (k6_subset_1 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.90/1.09  thf('59', plain,
% 0.90/1.09      (![X47 : $i, X48 : $i]:
% 0.90/1.09         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.09  thf('60', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.90/1.09      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.09  thf('61', plain,
% 0.90/1.09      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['57', '60'])).
% 0.90/1.09  thf(t1_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.90/1.09       ( r1_tarski @ A @ C ) ))).
% 0.90/1.09  thf('62', plain,
% 0.90/1.09      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.90/1.09         (~ (r1_tarski @ X8 @ X9)
% 0.90/1.09          | ~ (r1_tarski @ X9 @ X10)
% 0.90/1.09          | (r1_tarski @ X8 @ X10))),
% 0.90/1.09      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.90/1.09  thf('63', plain,
% 0.90/1.09      ((![X0 : $i]:
% 0.90/1.09          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.90/1.09           | ~ (r1_tarski @ sk_B @ X0)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['61', '62'])).
% 0.90/1.09  thf('64', plain,
% 0.90/1.09      ((![X0 : $i]:
% 0.90/1.09          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.09           (k3_tarski @ (k2_tarski @ sk_B @ X0))))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['54', '63'])).
% 0.90/1.09  thf('65', plain,
% 0.90/1.09      (![X47 : $i, X49 : $i]:
% 0.90/1.09         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.09  thf('66', plain,
% 0.90/1.09      ((![X0 : $i]:
% 0.90/1.09          (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.09           (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ sk_B @ X0)))))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['64', '65'])).
% 0.90/1.09  thf(commutativity_k2_tarski, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.90/1.09  thf('67', plain,
% 0.90/1.09      (![X22 : $i, X23 : $i]:
% 0.90/1.09         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 0.90/1.09      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.90/1.09  thf('68', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.90/1.09      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.09  thf('69', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('70', plain,
% 0.90/1.09      (![X47 : $i, X48 : $i]:
% 0.90/1.09         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.09  thf('71', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.09  thf('72', plain,
% 0.90/1.09      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.90/1.09         (~ (r1_tarski @ X8 @ X9)
% 0.90/1.09          | ~ (r1_tarski @ X9 @ X10)
% 0.90/1.09          | (r1_tarski @ X8 @ X10))),
% 0.90/1.09      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.90/1.09  thf('73', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['71', '72'])).
% 0.90/1.09  thf('74', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['68', '73'])).
% 0.90/1.09  thf('75', plain,
% 0.90/1.09      (![X47 : $i, X49 : $i]:
% 0.90/1.09         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.09  thf('76', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (m1_subset_1 @ sk_B @ 
% 0.90/1.09          (k1_zfmisc_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['74', '75'])).
% 0.90/1.09  thf('77', plain,
% 0.90/1.09      (![X24 : $i, X25 : $i]:
% 0.90/1.09         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 0.90/1.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.90/1.09  thf('78', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (m1_subset_1 @ sk_B @ 
% 0.90/1.09          (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ (u1_struct_0 @ sk_A) @ X0))))),
% 0.90/1.09      inference('demod', [status(thm)], ['76', '77'])).
% 0.90/1.09  thf('79', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (m1_subset_1 @ sk_B @ 
% 0.90/1.09          (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A)))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['67', '78'])).
% 0.90/1.09  thf(redefinition_k4_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.90/1.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.90/1.09       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.90/1.09  thf('80', plain,
% 0.90/1.09      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.90/1.09          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 0.90/1.09          | ((k4_subset_1 @ X36 @ X35 @ X37) = (k2_xboole_0 @ X35 @ X37)))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.90/1.09  thf('81', plain,
% 0.90/1.09      (![X24 : $i, X25 : $i]:
% 0.90/1.09         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 0.90/1.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.90/1.09  thf('82', plain,
% 0.90/1.09      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.90/1.09          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 0.90/1.09          | ((k4_subset_1 @ X36 @ X35 @ X37)
% 0.90/1.09              = (k3_tarski @ (k2_tarski @ X35 @ X37))))),
% 0.90/1.09      inference('demod', [status(thm)], ['80', '81'])).
% 0.90/1.09  thf('83', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (((k4_subset_1 @ 
% 0.90/1.09            (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))) @ sk_B @ X1)
% 0.90/1.09            = (k3_tarski @ (k2_tarski @ sk_B @ X1)))
% 0.90/1.09          | ~ (m1_subset_1 @ X1 @ 
% 0.90/1.09               (k1_zfmisc_1 @ 
% 0.90/1.09                (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['79', '82'])).
% 0.90/1.09  thf('84', plain,
% 0.90/1.09      ((((k4_subset_1 @ 
% 0.90/1.09          (k3_tarski @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_B @ 
% 0.90/1.09          (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['66', '83'])).
% 0.90/1.09  thf('85', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.09  thf(t12_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.90/1.09  thf('86', plain,
% 0.90/1.09      (![X5 : $i, X6 : $i]:
% 0.90/1.09         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.90/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.09  thf('87', plain,
% 0.90/1.09      (((k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['85', '86'])).
% 0.90/1.09  thf('88', plain,
% 0.90/1.09      (![X24 : $i, X25 : $i]:
% 0.90/1.09         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 0.90/1.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.90/1.09  thf('89', plain,
% 0.90/1.09      (((k3_tarski @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.90/1.09         = (u1_struct_0 @ sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['87', '88'])).
% 0.90/1.09  thf('90', plain,
% 0.90/1.09      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['57', '60'])).
% 0.90/1.09  thf('91', plain,
% 0.90/1.09      (![X5 : $i, X6 : $i]:
% 0.90/1.09         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.90/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.09  thf('92', plain,
% 0.90/1.09      (![X24 : $i, X25 : $i]:
% 0.90/1.09         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 0.90/1.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.90/1.09  thf('93', plain,
% 0.90/1.09      (![X5 : $i, X6 : $i]:
% 0.90/1.09         (((k3_tarski @ (k2_tarski @ X6 @ X5)) = (X5))
% 0.90/1.09          | ~ (r1_tarski @ X6 @ X5))),
% 0.90/1.09      inference('demod', [status(thm)], ['91', '92'])).
% 0.90/1.09  thf('94', plain,
% 0.90/1.09      ((((k3_tarski @ (k2_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)) = (sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['90', '93'])).
% 0.90/1.09  thf('95', plain,
% 0.90/1.09      (![X22 : $i, X23 : $i]:
% 0.90/1.09         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 0.90/1.09      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.90/1.09  thf('96', plain,
% 0.90/1.09      ((((k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('demod', [status(thm)], ['94', '95'])).
% 0.90/1.09  thf('97', plain,
% 0.90/1.09      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('demod', [status(thm)], ['84', '89', '96'])).
% 0.90/1.09  thf('98', plain,
% 0.90/1.09      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['51', '97'])).
% 0.90/1.09  thf('99', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t52_pre_topc, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( l1_pre_topc @ A ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.90/1.09             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.90/1.09               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.90/1.09  thf('100', plain,
% 0.90/1.09      (![X50 : $i, X51 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.90/1.09          | ~ (v2_pre_topc @ X51)
% 0.90/1.09          | ((k2_pre_topc @ X51 @ X50) != (X50))
% 0.90/1.09          | (v4_pre_topc @ X50 @ X51)
% 0.90/1.09          | ~ (l1_pre_topc @ X51))),
% 0.90/1.09      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.90/1.09  thf('101', plain,
% 0.90/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.09        | (v4_pre_topc @ sk_B @ sk_A)
% 0.90/1.09        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.90/1.09        | ~ (v2_pre_topc @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['99', '100'])).
% 0.90/1.09  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('104', plain,
% 0.90/1.09      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.90/1.09  thf('105', plain,
% 0.90/1.09      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['98', '104'])).
% 0.90/1.09  thf('106', plain,
% 0.90/1.09      (((v4_pre_topc @ sk_B @ sk_A))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('simplify', [status(thm)], ['105'])).
% 0.90/1.09  thf('107', plain,
% 0.90/1.09      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('split', [status(esa)], ['0'])).
% 0.90/1.09  thf('108', plain,
% 0.90/1.09      (~
% 0.90/1.09       (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.90/1.09       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['106', '107'])).
% 0.90/1.09  thf('109', plain, ($false),
% 0.90/1.09      inference('sat_resolution*', [status(thm)], ['1', '45', '46', '108'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
