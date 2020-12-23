%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FrZ8BcGnOe

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:36 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 203 expanded)
%              Number of leaves         :   37 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  922 (2292 expanded)
%              Number of equality atoms :   64 ( 133 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k6_subset_1 @ X21 @ X23 ) ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ ( k6_subset_1 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['28','33'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('49',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X29 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('50',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('55',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('60',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['28','33'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['68','69'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('72',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['67','76'])).

thf('78',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['58','77'])).

thf('79',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['53','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['47','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FrZ8BcGnOe
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 21:05:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.56/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.77  % Solved by: fo/fo7.sh
% 0.56/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.77  % done 988 iterations in 0.299s
% 0.56/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.77  % SZS output start Refutation
% 0.56/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.77  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.56/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.77  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.56/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.77  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.56/0.77  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.56/0.77  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.56/0.77  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.56/0.77  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.56/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.56/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.56/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.56/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.56/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.77  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.56/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.56/0.77  thf(t77_tops_1, conjecture,
% 0.56/0.77    (![A:$i]:
% 0.56/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.56/0.77       ( ![B:$i]:
% 0.56/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.77           ( ( v4_pre_topc @ B @ A ) <=>
% 0.56/0.77             ( ( k2_tops_1 @ A @ B ) =
% 0.56/0.77               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.56/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.77    (~( ![A:$i]:
% 0.56/0.77        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.56/0.77          ( ![B:$i]:
% 0.56/0.77            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.77              ( ( v4_pre_topc @ B @ A ) <=>
% 0.56/0.77                ( ( k2_tops_1 @ A @ B ) =
% 0.56/0.77                  ( k7_subset_1 @
% 0.56/0.77                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.56/0.77    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.56/0.77  thf('0', plain,
% 0.56/0.77      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77              (k1_tops_1 @ sk_A @ sk_B)))
% 0.56/0.77        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('1', plain,
% 0.56/0.77      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.56/0.77      inference('split', [status(esa)], ['0'])).
% 0.56/0.77  thf('2', plain,
% 0.56/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(t74_tops_1, axiom,
% 0.56/0.77    (![A:$i]:
% 0.56/0.77     ( ( l1_pre_topc @ A ) =>
% 0.56/0.77       ( ![B:$i]:
% 0.56/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.77           ( ( k1_tops_1 @ A @ B ) =
% 0.56/0.77             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.56/0.77  thf('3', plain,
% 0.56/0.77      (![X35 : $i, X36 : $i]:
% 0.56/0.77         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.56/0.77          | ((k1_tops_1 @ X36 @ X35)
% 0.56/0.77              = (k7_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 0.56/0.77                 (k2_tops_1 @ X36 @ X35)))
% 0.56/0.77          | ~ (l1_pre_topc @ X36))),
% 0.56/0.77      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.56/0.77  thf('4', plain,
% 0.56/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.56/0.77        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.56/0.77            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.56/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.77  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('6', plain,
% 0.56/0.77      (((k1_tops_1 @ sk_A @ sk_B)
% 0.56/0.77         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.56/0.77      inference('demod', [status(thm)], ['4', '5'])).
% 0.56/0.77  thf('7', plain,
% 0.56/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(redefinition_k7_subset_1, axiom,
% 0.56/0.77    (![A:$i,B:$i,C:$i]:
% 0.56/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.77       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.56/0.77  thf('8', plain,
% 0.56/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.56/0.77         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.56/0.77          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.56/0.77      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.56/0.77  thf(redefinition_k6_subset_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.56/0.77  thf('9', plain,
% 0.56/0.77      (![X19 : $i, X20 : $i]:
% 0.56/0.77         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.56/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.56/0.77  thf('10', plain,
% 0.56/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.56/0.77         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.56/0.77          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k6_subset_1 @ X21 @ X23)))),
% 0.56/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.56/0.77  thf('11', plain,
% 0.56/0.77      (![X0 : $i]:
% 0.56/0.77         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.56/0.77           = (k6_subset_1 @ sk_B @ X0))),
% 0.56/0.77      inference('sup-', [status(thm)], ['7', '10'])).
% 0.56/0.77  thf('12', plain,
% 0.56/0.77      (((k1_tops_1 @ sk_A @ sk_B)
% 0.56/0.77         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.56/0.77      inference('demod', [status(thm)], ['6', '11'])).
% 0.56/0.77  thf(t48_xboole_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.56/0.77  thf('13', plain,
% 0.56/0.77      (![X8 : $i, X9 : $i]:
% 0.56/0.77         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.56/0.77           = (k3_xboole_0 @ X8 @ X9))),
% 0.56/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.77  thf('14', plain,
% 0.56/0.77      (![X19 : $i, X20 : $i]:
% 0.56/0.77         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.56/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.56/0.77  thf('15', plain,
% 0.56/0.77      (![X19 : $i, X20 : $i]:
% 0.56/0.77         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.56/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.56/0.77  thf('16', plain,
% 0.56/0.77      (![X8 : $i, X9 : $i]:
% 0.56/0.77         ((k6_subset_1 @ X8 @ (k6_subset_1 @ X8 @ X9))
% 0.56/0.77           = (k3_xboole_0 @ X8 @ X9))),
% 0.56/0.77      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.56/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.56/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.56/0.77  thf('17', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.56/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.77  thf('18', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k3_xboole_0 @ X0 @ X1)
% 0.56/0.77           = (k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.56/0.77      inference('sup+', [status(thm)], ['16', '17'])).
% 0.56/0.77  thf('19', plain,
% 0.56/0.77      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.56/0.77         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.56/0.77      inference('sup+', [status(thm)], ['12', '18'])).
% 0.56/0.77  thf('20', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.56/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.77  thf('21', plain,
% 0.56/0.77      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.56/0.77         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.56/0.77      inference('demod', [status(thm)], ['19', '20'])).
% 0.56/0.77  thf('22', plain,
% 0.56/0.77      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77             (k1_tops_1 @ sk_A @ sk_B)))
% 0.56/0.77        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('23', plain,
% 0.56/0.77      (![X0 : $i]:
% 0.56/0.77         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.56/0.77           = (k6_subset_1 @ sk_B @ X0))),
% 0.56/0.77      inference('sup-', [status(thm)], ['7', '10'])).
% 0.56/0.77  thf('24', plain,
% 0.56/0.77      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.56/0.77        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.56/0.77      inference('demod', [status(thm)], ['22', '23'])).
% 0.56/0.77  thf(dt_k6_subset_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.56/0.77  thf('25', plain,
% 0.56/0.77      (![X14 : $i, X15 : $i]:
% 0.56/0.77         (m1_subset_1 @ (k6_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))),
% 0.56/0.77      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.56/0.77  thf(t3_subset, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.56/0.77  thf('26', plain,
% 0.56/0.77      (![X24 : $i, X25 : $i]:
% 0.56/0.77         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.56/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.77  thf('27', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.56/0.77      inference('sup-', [status(thm)], ['25', '26'])).
% 0.56/0.77  thf('28', plain,
% 0.56/0.77      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.56/0.77        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.56/0.77      inference('sup+', [status(thm)], ['24', '27'])).
% 0.56/0.77  thf('29', plain,
% 0.56/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(t69_tops_1, axiom,
% 0.56/0.77    (![A:$i]:
% 0.56/0.77     ( ( l1_pre_topc @ A ) =>
% 0.56/0.77       ( ![B:$i]:
% 0.56/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.77           ( ( v4_pre_topc @ B @ A ) =>
% 0.56/0.77             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.56/0.77  thf('30', plain,
% 0.56/0.77      (![X33 : $i, X34 : $i]:
% 0.56/0.77         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.56/0.77          | (r1_tarski @ (k2_tops_1 @ X34 @ X33) @ X33)
% 0.56/0.77          | ~ (v4_pre_topc @ X33 @ X34)
% 0.56/0.77          | ~ (l1_pre_topc @ X34))),
% 0.56/0.77      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.56/0.77  thf('31', plain,
% 0.56/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.56/0.77        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.56/0.77        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.56/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.56/0.77  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('33', plain,
% 0.56/0.77      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.56/0.77        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.56/0.77      inference('demod', [status(thm)], ['31', '32'])).
% 0.56/0.77  thf('34', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.56/0.77      inference('clc', [status(thm)], ['28', '33'])).
% 0.56/0.77  thf(t28_xboole_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.56/0.77  thf('35', plain,
% 0.56/0.77      (![X6 : $i, X7 : $i]:
% 0.56/0.77         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.56/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.56/0.77  thf('36', plain,
% 0.56/0.77      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.56/0.77         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.56/0.77      inference('sup-', [status(thm)], ['34', '35'])).
% 0.56/0.77  thf('37', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.56/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.56/0.77  thf('38', plain,
% 0.56/0.77      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.56/0.77         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.56/0.77      inference('demod', [status(thm)], ['36', '37'])).
% 0.56/0.77  thf('39', plain,
% 0.56/0.77      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.56/0.77         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.56/0.77      inference('sup+', [status(thm)], ['21', '38'])).
% 0.56/0.77  thf('40', plain,
% 0.56/0.77      (![X0 : $i]:
% 0.56/0.77         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.56/0.77           = (k6_subset_1 @ sk_B @ X0))),
% 0.56/0.77      inference('sup-', [status(thm)], ['7', '10'])).
% 0.56/0.77  thf('41', plain,
% 0.56/0.77      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77              (k1_tops_1 @ sk_A @ sk_B))))
% 0.56/0.77         <= (~
% 0.56/0.77             (((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.56/0.77      inference('split', [status(esa)], ['0'])).
% 0.56/0.77  thf('42', plain,
% 0.56/0.77      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.56/0.77         <= (~
% 0.56/0.77             (((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.56/0.77      inference('sup-', [status(thm)], ['40', '41'])).
% 0.56/0.77  thf('43', plain,
% 0.56/0.77      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.56/0.77         <= (~
% 0.56/0.77             (((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.56/0.77      inference('sup-', [status(thm)], ['39', '42'])).
% 0.56/0.77  thf('44', plain,
% 0.56/0.77      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.56/0.77      inference('simplify', [status(thm)], ['43'])).
% 0.56/0.77  thf('45', plain,
% 0.56/0.77      (~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.56/0.77       ~
% 0.56/0.77       (((k2_tops_1 @ sk_A @ sk_B)
% 0.56/0.77          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.56/0.77      inference('split', [status(esa)], ['0'])).
% 0.56/0.77  thf('46', plain, (~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.56/0.77      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.56/0.77  thf('47', plain, (~ (v4_pre_topc @ sk_B @ sk_A)),
% 0.56/0.77      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.56/0.77  thf('48', plain,
% 0.56/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(fc1_tops_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.56/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.56/0.77       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.56/0.77  thf('49', plain,
% 0.56/0.77      (![X29 : $i, X30 : $i]:
% 0.56/0.77         (~ (l1_pre_topc @ X29)
% 0.56/0.77          | ~ (v2_pre_topc @ X29)
% 0.56/0.77          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.56/0.77          | (v4_pre_topc @ (k2_pre_topc @ X29 @ X30) @ X29))),
% 0.56/0.77      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.56/0.77  thf('50', plain,
% 0.56/0.77      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.56/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.56/0.77        | ~ (l1_pre_topc @ sk_A))),
% 0.56/0.77      inference('sup-', [status(thm)], ['48', '49'])).
% 0.56/0.77  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('53', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.56/0.77      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.56/0.77  thf('54', plain,
% 0.56/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(t65_tops_1, axiom,
% 0.56/0.77    (![A:$i]:
% 0.56/0.77     ( ( l1_pre_topc @ A ) =>
% 0.56/0.77       ( ![B:$i]:
% 0.56/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.56/0.77           ( ( k2_pre_topc @ A @ B ) =
% 0.56/0.77             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.56/0.77  thf('55', plain,
% 0.56/0.77      (![X31 : $i, X32 : $i]:
% 0.56/0.77         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.56/0.77          | ((k2_pre_topc @ X32 @ X31)
% 0.56/0.77              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.56/0.77                 (k2_tops_1 @ X32 @ X31)))
% 0.56/0.77          | ~ (l1_pre_topc @ X32))),
% 0.56/0.77      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.56/0.77  thf('56', plain,
% 0.56/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.56/0.77        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.56/0.77            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.56/0.77      inference('sup-', [status(thm)], ['54', '55'])).
% 0.56/0.77  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('58', plain,
% 0.56/0.77      (((k2_pre_topc @ sk_A @ sk_B)
% 0.56/0.77         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.56/0.77            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.56/0.77      inference('demod', [status(thm)], ['56', '57'])).
% 0.56/0.77  thf('59', plain,
% 0.56/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(dt_k2_tops_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( ( l1_pre_topc @ A ) & 
% 0.56/0.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.56/0.77       ( m1_subset_1 @
% 0.56/0.77         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.56/0.77  thf('60', plain,
% 0.56/0.77      (![X27 : $i, X28 : $i]:
% 0.56/0.77         (~ (l1_pre_topc @ X27)
% 0.56/0.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.56/0.77          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 0.56/0.77             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 0.56/0.77      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.56/0.77  thf('61', plain,
% 0.56/0.77      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.56/0.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.56/0.77        | ~ (l1_pre_topc @ sk_A))),
% 0.56/0.77      inference('sup-', [status(thm)], ['59', '60'])).
% 0.56/0.77  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf('63', plain,
% 0.56/0.77      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.56/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.77      inference('demod', [status(thm)], ['61', '62'])).
% 0.56/0.77  thf('64', plain,
% 0.56/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.56/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.77  thf(redefinition_k4_subset_1, axiom,
% 0.56/0.77    (![A:$i,B:$i,C:$i]:
% 0.56/0.77     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.56/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.77       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.56/0.77  thf('65', plain,
% 0.56/0.77      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.56/0.77         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.56/0.77          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 0.56/0.77          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 0.56/0.77      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.56/0.77  thf('66', plain,
% 0.56/0.77      (![X0 : $i]:
% 0.56/0.77         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.56/0.77            = (k2_xboole_0 @ sk_B @ X0))
% 0.56/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.56/0.77      inference('sup-', [status(thm)], ['64', '65'])).
% 0.56/0.77  thf('67', plain,
% 0.56/0.77      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.56/0.77         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.56/0.77      inference('sup-', [status(thm)], ['63', '66'])).
% 0.56/0.77  thf('68', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.56/0.77      inference('clc', [status(thm)], ['28', '33'])).
% 0.56/0.77  thf(t12_xboole_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.56/0.77  thf('69', plain,
% 0.56/0.77      (![X4 : $i, X5 : $i]:
% 0.56/0.77         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.56/0.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.56/0.77  thf('70', plain,
% 0.56/0.77      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 0.56/0.77      inference('sup-', [status(thm)], ['68', '69'])).
% 0.56/0.77  thf(commutativity_k2_tarski, axiom,
% 0.56/0.77    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.56/0.77  thf('71', plain,
% 0.56/0.77      (![X10 : $i, X11 : $i]:
% 0.56/0.77         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.56/0.77      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.56/0.77  thf(l51_zfmisc_1, axiom,
% 0.56/0.77    (![A:$i,B:$i]:
% 0.56/0.77     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.56/0.77  thf('72', plain,
% 0.56/0.77      (![X12 : $i, X13 : $i]:
% 0.56/0.77         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 0.56/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.56/0.77  thf('73', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]:
% 0.56/0.77         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.77      inference('sup+', [status(thm)], ['71', '72'])).
% 0.56/0.77  thf('74', plain,
% 0.56/0.77      (![X12 : $i, X13 : $i]:
% 0.56/0.77         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 0.56/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.56/0.77  thf('75', plain,
% 0.56/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.56/0.77      inference('sup+', [status(thm)], ['73', '74'])).
% 0.56/0.77  thf('76', plain,
% 0.56/0.77      (((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.56/0.77      inference('demod', [status(thm)], ['70', '75'])).
% 0.56/0.77  thf('77', plain,
% 0.56/0.77      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.56/0.77         = (sk_B))),
% 0.56/0.77      inference('demod', [status(thm)], ['67', '76'])).
% 0.56/0.77  thf('78', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.56/0.77      inference('sup+', [status(thm)], ['58', '77'])).
% 0.56/0.77  thf('79', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.56/0.77      inference('demod', [status(thm)], ['53', '78'])).
% 0.56/0.77  thf('80', plain, ($false), inference('demod', [status(thm)], ['47', '79'])).
% 0.56/0.77  
% 0.56/0.77  % SZS output end Refutation
% 0.56/0.77  
% 0.56/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
