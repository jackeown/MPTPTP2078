%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dk6I4Sk3Kj

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:43 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 269 expanded)
%              Number of leaves         :   33 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  923 (3290 expanded)
%              Number of equality atoms :   65 ( 192 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k2_tops_1 @ X58 @ X57 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X58 ) @ ( k2_pre_topc @ X58 @ X57 ) @ ( k1_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v4_pre_topc @ X51 @ X52 )
      | ( ( k2_pre_topc @ X52 @ X51 )
        = X51 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k2_pre_topc @ X60 @ X59 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 @ ( k2_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k4_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X38 @ X37 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k4_subset_1 @ X41 @ X40 @ X42 )
        = ( k2_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X36 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('35',plain,(
    ! [X35: $i] :
      ( ( k2_subset_1 @ X35 )
      = X35 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X38 @ X37 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('50',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k4_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['33','52'])).

thf('54',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['24','53'])).

thf('55',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('57',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( l1_pre_topc @ X55 )
      | ~ ( v2_pre_topc @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X55 @ X56 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('58',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','61'])).

thf('63',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('64',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('66',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','64','65'])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['12','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('69',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','67','68'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('72',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['14','64'])).

thf('74',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dk6I4Sk3Kj
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:56:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 306 iterations in 0.149s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.62  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.38/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.62  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.62  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(t77_tops_1, conjecture,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.62             ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.62               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i]:
% 0.38/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.62          ( ![B:$i]:
% 0.38/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62              ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.62                ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.62                  ( k7_subset_1 @
% 0.38/0.62                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(l78_tops_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( l1_pre_topc @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62           ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.62             ( k7_subset_1 @
% 0.38/0.62               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.38/0.62               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X57 : $i, X58 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.38/0.62          | ((k2_tops_1 @ X58 @ X57)
% 0.38/0.62              = (k7_subset_1 @ (u1_struct_0 @ X58) @ 
% 0.38/0.62                 (k2_pre_topc @ X58 @ X57) @ (k1_tops_1 @ X58 @ X57)))
% 0.38/0.62          | ~ (l1_pre_topc @ X58))),
% 0.38/0.62      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.62  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.38/0.62            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62             (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.62        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.62      inference('split', [status(esa)], ['5'])).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t52_pre_topc, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( l1_pre_topc @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.38/0.62             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.38/0.62               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X51 : $i, X52 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.38/0.62          | ~ (v4_pre_topc @ X51 @ X52)
% 0.38/0.62          | ((k2_pre_topc @ X52 @ X51) = (X51))
% 0.38/0.62          | ~ (l1_pre_topc @ X52))),
% 0.38/0.62      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.38/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.38/0.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '11'])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62              (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.62        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (~
% 0.38/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.38/0.62       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.62      inference('split', [status(esa)], ['13'])).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t65_tops_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( l1_pre_topc @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.62           ( ( k2_pre_topc @ A @ B ) =
% 0.38/0.62             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X59 : $i, X60 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 0.38/0.62          | ((k2_pre_topc @ X60 @ X59)
% 0.38/0.62              = (k4_subset_1 @ (u1_struct_0 @ X60) @ X59 @ 
% 0.38/0.62                 (k2_tops_1 @ X60 @ X59)))
% 0.38/0.62          | ~ (l1_pre_topc @ X60))),
% 0.38/0.62      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.62        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.38/0.62            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.62  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (((k2_pre_topc @ sk_A @ sk_B)
% 0.38/0.62         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(redefinition_k7_subset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.62       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.38/0.62          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k4_xboole_0 @ X43 @ X45)))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62             (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('split', [status(esa)], ['5'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(dt_k7_subset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.62       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.38/0.62          | (m1_subset_1 @ (k7_subset_1 @ X38 @ X37 @ X39) @ 
% 0.38/0.62             (k1_zfmisc_1 @ X38)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.38/0.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.38/0.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(redefinition_k4_subset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.38/0.62          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41))
% 0.38/0.62          | ((k4_subset_1 @ X41 @ X40 @ X42) = (k2_xboole_0 @ X40 @ X42)))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.62            = (k2_xboole_0 @ sk_B @ X0))
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62           (k4_xboole_0 @ sk_B @ X0))
% 0.38/0.62           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['29', '32'])).
% 0.38/0.62  thf(dt_k2_subset_1, axiom,
% 0.38/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (![X36 : $i]: (m1_subset_1 @ (k2_subset_1 @ X36) @ (k1_zfmisc_1 @ X36))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.38/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.62  thf('35', plain, (![X35 : $i]: ((k2_subset_1 @ X35) = (X35))),
% 0.38/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.62  thf('36', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.38/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.38/0.62          | (m1_subset_1 @ (k7_subset_1 @ X38 @ X37 @ X39) @ 
% 0.38/0.62             (k1_zfmisc_1 @ X38)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.62  thf(t3_subset, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (![X48 : $i, X49 : $i]:
% 0.38/0.62         ((r1_tarski @ X48 @ X49) | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k7_subset_1 @ X0 @ X0 @ X1) @ X0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.62  thf(t12_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.62  thf('41', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i]:
% 0.38/0.62         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.38/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ (k7_subset_1 @ X0 @ X0 @ X1) @ X0) = (X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.62  thf(commutativity_k2_tarski, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.62  thf(l51_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('44', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 0.38/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.62  thf('45', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['43', '44'])).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i]:
% 0.38/0.62         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 0.38/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['45', '46'])).
% 0.38/0.62  thf('48', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1)) = (X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['42', '47'])).
% 0.38/0.62  thf('49', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.38/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.62  thf('50', plain,
% 0.38/0.62      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.38/0.62          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k4_xboole_0 @ X43 @ X45)))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.62  thf('52', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['48', '51'])).
% 0.38/0.62  thf('53', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62           (k4_xboole_0 @ sk_B @ X0)) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['33', '52'])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.62          = (sk_B)))
% 0.38/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup+', [status(thm)], ['24', '53'])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.38/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup+', [status(thm)], ['19', '54'])).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(fc1_tops_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.38/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.62       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.38/0.62  thf('57', plain,
% 0.38/0.62      (![X55 : $i, X56 : $i]:
% 0.38/0.62         (~ (l1_pre_topc @ X55)
% 0.38/0.62          | ~ (v2_pre_topc @ X55)
% 0.38/0.62          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 0.38/0.62          | (v4_pre_topc @ (k2_pre_topc @ X55 @ X56) @ X55))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.38/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.62  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('61', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.38/0.62      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.38/0.62  thf('62', plain,
% 0.38/0.62      (((v4_pre_topc @ sk_B @ sk_A))
% 0.38/0.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup+', [status(thm)], ['55', '61'])).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.62      inference('split', [status(esa)], ['13'])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.38/0.62       ~
% 0.38/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.62  thf('65', plain,
% 0.38/0.62      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.38/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('split', [status(esa)], ['5'])).
% 0.38/0.62  thf('66', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.62      inference('sat_resolution*', [status(thm)], ['14', '64', '65'])).
% 0.38/0.62  thf('67', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.62      inference('simpl_trail', [status(thm)], ['12', '66'])).
% 0.38/0.62  thf('68', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.62  thf('69', plain,
% 0.38/0.62      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['4', '67', '68'])).
% 0.38/0.62  thf('70', plain,
% 0.38/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62              (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.62         <= (~
% 0.38/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('split', [status(esa)], ['13'])).
% 0.38/0.62  thf('71', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.62           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.62  thf('72', plain,
% 0.38/0.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.62         <= (~
% 0.38/0.62             (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('demod', [status(thm)], ['70', '71'])).
% 0.38/0.62  thf('73', plain,
% 0.38/0.62      (~
% 0.38/0.62       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.62             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sat_resolution*', [status(thm)], ['14', '64'])).
% 0.38/0.62  thf('74', plain,
% 0.38/0.62      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.62         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('simpl_trail', [status(thm)], ['72', '73'])).
% 0.38/0.62  thf('75', plain, ($false),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['69', '74'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.49/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
