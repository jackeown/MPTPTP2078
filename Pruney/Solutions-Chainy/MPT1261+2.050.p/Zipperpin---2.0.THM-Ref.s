%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GGoLeLV2eS

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:44 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 956 expanded)
%              Number of leaves         :   45 ( 326 expanded)
%              Depth                    :   18
%              Number of atoms          : 1514 (9250 expanded)
%              Number of equality atoms :  129 ( 811 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k2_tops_1 @ X48 @ X47 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X48 ) @ ( k2_pre_topc @ X48 @ X47 ) @ ( k1_tops_1 @ X48 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
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

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k6_subset_1 @ X33 @ X34 )
      = ( k4_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k6_subset_1 @ X33 @ X34 )
      = ( k4_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k6_subset_1 @ X33 @ X34 )
      = ( k4_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ ( k6_subset_1 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k2_pre_topc @ X52 @ X51 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X52 ) @ X51 @ ( k2_tops_1 @ X52 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k2_tops_1 @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('33',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('35',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k4_subset_1 @ X31 @ X30 @ X32 )
        = ( k2_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33','42','43'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('48',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X54 @ X53 ) @ X53 )
      | ~ ( v4_pre_topc @ X53 @ X54 )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('54',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('56',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('57',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('59',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k6_subset_1 @ X33 @ X34 )
      = ( k4_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('63',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k6_subset_1 @ X33 @ X34 )
      = ( k4_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['62','63','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('72',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','78'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('80',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('81',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k6_subset_1 @ X33 @ X34 )
      = ( k4_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('82',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k6_subset_1 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('86',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['44','86'])).

thf('88',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33','42','43'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('92',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X35 @ X37 )
        = ( k4_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('93',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k6_subset_1 @ X33 @ X34 )
      = ( k4_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('94',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X35 @ X37 )
        = ( k6_subset_1 @ X35 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('97',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('98',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('99',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k6_subset_1 @ X33 @ X34 )
      = ( k4_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('100',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('103',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('105',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('107',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k6_subset_1 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('109',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('112',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('115',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X45 @ X46 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('116',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['88'])).

thf('122',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['45'])).

thf('124',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['89','122','123'])).

thf('125',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['87','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('127',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','125','126'])).

thf('128',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['88'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('130',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['89','122'])).

thf('132',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['127','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GGoLeLV2eS
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:47:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.25  % Solved by: fo/fo7.sh
% 1.05/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.25  % done 3060 iterations in 0.799s
% 1.05/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.25  % SZS output start Refutation
% 1.05/1.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.25  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.05/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.25  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.05/1.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.05/1.25  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.05/1.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.25  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.05/1.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.05/1.25  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.05/1.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.25  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.05/1.25  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.05/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.05/1.25  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.05/1.25  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.05/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.05/1.25  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.05/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.25  thf(t77_tops_1, conjecture,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( ( v4_pre_topc @ B @ A ) <=>
% 1.05/1.25             ( ( k2_tops_1 @ A @ B ) =
% 1.05/1.25               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.05/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.25    (~( ![A:$i]:
% 1.05/1.25        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.05/1.25          ( ![B:$i]:
% 1.05/1.25            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25              ( ( v4_pre_topc @ B @ A ) <=>
% 1.05/1.25                ( ( k2_tops_1 @ A @ B ) =
% 1.05/1.25                  ( k7_subset_1 @
% 1.05/1.25                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.05/1.25    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.05/1.25  thf('0', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(l78_tops_1, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( l1_pre_topc @ A ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( ( k2_tops_1 @ A @ B ) =
% 1.05/1.25             ( k7_subset_1 @
% 1.05/1.25               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.05/1.25               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.05/1.25  thf('1', plain,
% 1.05/1.25      (![X47 : $i, X48 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 1.05/1.25          | ((k2_tops_1 @ X48 @ X47)
% 1.05/1.25              = (k7_subset_1 @ (u1_struct_0 @ X48) @ 
% 1.05/1.25                 (k2_pre_topc @ X48 @ X47) @ (k1_tops_1 @ X48 @ X47)))
% 1.05/1.25          | ~ (l1_pre_topc @ X48))),
% 1.05/1.25      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.05/1.25  thf('2', plain,
% 1.05/1.25      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.25        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.25               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['0', '1'])).
% 1.05/1.25  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('4', plain,
% 1.05/1.25      (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.05/1.25            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.25      inference('demod', [status(thm)], ['2', '3'])).
% 1.05/1.25  thf('5', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(t3_subset, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.05/1.25  thf('6', plain,
% 1.05/1.25      (![X40 : $i, X41 : $i]:
% 1.05/1.25         ((r1_tarski @ X40 @ X41) | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t3_subset])).
% 1.05/1.25  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.25  thf(t28_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.05/1.25  thf('8', plain,
% 1.05/1.25      (![X6 : $i, X7 : $i]:
% 1.05/1.25         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.05/1.25      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.25  thf('9', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.05/1.25      inference('sup-', [status(thm)], ['7', '8'])).
% 1.05/1.25  thf(commutativity_k2_tarski, axiom,
% 1.05/1.25    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.05/1.25  thf('10', plain,
% 1.05/1.25      (![X18 : $i, X19 : $i]:
% 1.05/1.25         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 1.05/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.05/1.25  thf(t12_setfam_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.05/1.25  thf('11', plain,
% 1.05/1.25      (![X38 : $i, X39 : $i]:
% 1.05/1.25         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 1.05/1.25      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.05/1.25  thf('12', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['10', '11'])).
% 1.05/1.25  thf('13', plain,
% 1.05/1.25      (![X38 : $i, X39 : $i]:
% 1.05/1.25         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 1.05/1.25      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.05/1.25  thf('14', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['12', '13'])).
% 1.05/1.25  thf(t100_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.05/1.25  thf('15', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k4_xboole_0 @ X0 @ X1)
% 1.05/1.25           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.25  thf(redefinition_k6_subset_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.05/1.25  thf('16', plain,
% 1.05/1.25      (![X33 : $i, X34 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.05/1.25  thf('17', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X0 @ X1)
% 1.05/1.25           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.05/1.25  thf('18', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X0 @ X1)
% 1.05/1.25           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.05/1.25      inference('sup+', [status(thm)], ['14', '17'])).
% 1.05/1.25  thf('19', plain,
% 1.05/1.25      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.05/1.25         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.05/1.25      inference('sup+', [status(thm)], ['9', '18'])).
% 1.05/1.25  thf(t48_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.05/1.25  thf('20', plain,
% 1.05/1.25      (![X14 : $i, X15 : $i]:
% 1.05/1.25         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.05/1.25           = (k3_xboole_0 @ X14 @ X15))),
% 1.05/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.25  thf('21', plain,
% 1.05/1.25      (![X33 : $i, X34 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.05/1.25  thf('22', plain,
% 1.05/1.25      (![X33 : $i, X34 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.05/1.25  thf('23', plain,
% 1.05/1.25      (![X14 : $i, X15 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X14 @ (k6_subset_1 @ X14 @ X15))
% 1.05/1.25           = (k3_xboole_0 @ X14 @ X15))),
% 1.05/1.25      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.05/1.25  thf('24', plain,
% 1.05/1.25      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.25         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.05/1.25         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.05/1.25      inference('sup+', [status(thm)], ['19', '23'])).
% 1.05/1.25  thf('25', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['12', '13'])).
% 1.05/1.25  thf('26', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.05/1.25      inference('sup-', [status(thm)], ['7', '8'])).
% 1.05/1.25  thf('27', plain,
% 1.05/1.25      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.25         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.05/1.25  thf(dt_k6_subset_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.05/1.25  thf('28', plain,
% 1.05/1.25      (![X26 : $i, X27 : $i]:
% 1.05/1.25         (m1_subset_1 @ (k6_subset_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))),
% 1.05/1.25      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.05/1.25  thf(t65_tops_1, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( l1_pre_topc @ A ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( ( k2_pre_topc @ A @ B ) =
% 1.05/1.25             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.05/1.25  thf('29', plain,
% 1.05/1.25      (![X51 : $i, X52 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 1.05/1.25          | ((k2_pre_topc @ X52 @ X51)
% 1.05/1.25              = (k4_subset_1 @ (u1_struct_0 @ X52) @ X51 @ 
% 1.05/1.25                 (k2_tops_1 @ X52 @ X51)))
% 1.05/1.25          | ~ (l1_pre_topc @ X52))),
% 1.05/1.25      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.05/1.25  thf('30', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (l1_pre_topc @ X0)
% 1.05/1.25          | ((k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1))
% 1.05/1.25              = (k4_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.05/1.25                 (k6_subset_1 @ (u1_struct_0 @ X0) @ X1) @ 
% 1.05/1.25                 (k2_tops_1 @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1)))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['28', '29'])).
% 1.05/1.25  thf('31', plain,
% 1.05/1.25      ((((k2_pre_topc @ sk_A @ 
% 1.05/1.25          (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.25           (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.05/1.25          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25             (k2_tops_1 @ sk_A @ 
% 1.05/1.25              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.25               (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 1.05/1.25        | ~ (l1_pre_topc @ sk_A))),
% 1.05/1.25      inference('sup+', [status(thm)], ['27', '30'])).
% 1.05/1.25  thf('32', plain,
% 1.05/1.25      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.25         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.05/1.25  thf('33', plain,
% 1.05/1.25      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.05/1.25         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.05/1.25  thf('34', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(dt_k2_tops_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ( l1_pre_topc @ A ) & 
% 1.05/1.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.25       ( m1_subset_1 @
% 1.05/1.25         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.05/1.25  thf('35', plain,
% 1.05/1.25      (![X43 : $i, X44 : $i]:
% 1.05/1.25         (~ (l1_pre_topc @ X43)
% 1.05/1.25          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.05/1.25          | (m1_subset_1 @ (k2_tops_1 @ X43 @ X44) @ 
% 1.05/1.25             (k1_zfmisc_1 @ (u1_struct_0 @ X43))))),
% 1.05/1.25      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.05/1.25  thf('36', plain,
% 1.05/1.25      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.25        | ~ (l1_pre_topc @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['34', '35'])).
% 1.05/1.25  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('38', plain,
% 1.05/1.25      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['36', '37'])).
% 1.05/1.25  thf('39', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(redefinition_k4_subset_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.05/1.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.05/1.25       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.05/1.25  thf('40', plain,
% 1.05/1.25      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 1.05/1.25          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31))
% 1.05/1.25          | ((k4_subset_1 @ X31 @ X30 @ X32) = (k2_xboole_0 @ X30 @ X32)))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.05/1.25  thf('41', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.05/1.25            = (k2_xboole_0 @ sk_B @ X0))
% 1.05/1.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.25  thf('42', plain,
% 1.05/1.25      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.05/1.25         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['38', '41'])).
% 1.05/1.25  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('44', plain,
% 1.05/1.25      (((k2_pre_topc @ sk_A @ sk_B)
% 1.05/1.25         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.25      inference('demod', [status(thm)], ['31', '32', '33', '42', '43'])).
% 1.05/1.25  thf('45', plain,
% 1.05/1.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25             (k1_tops_1 @ sk_A @ sk_B)))
% 1.05/1.25        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('46', plain,
% 1.05/1.25      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.25      inference('split', [status(esa)], ['45'])).
% 1.05/1.25  thf('47', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(t69_tops_1, axiom,
% 1.05/1.25    (![A:$i]:
% 1.05/1.25     ( ( l1_pre_topc @ A ) =>
% 1.05/1.25       ( ![B:$i]:
% 1.05/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.25           ( ( v4_pre_topc @ B @ A ) =>
% 1.05/1.25             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.05/1.25  thf('48', plain,
% 1.05/1.25      (![X53 : $i, X54 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.05/1.25          | (r1_tarski @ (k2_tops_1 @ X54 @ X53) @ X53)
% 1.05/1.25          | ~ (v4_pre_topc @ X53 @ X54)
% 1.05/1.25          | ~ (l1_pre_topc @ X54))),
% 1.05/1.25      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.05/1.25  thf('49', plain,
% 1.05/1.25      ((~ (l1_pre_topc @ sk_A)
% 1.05/1.25        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.05/1.25        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.05/1.25      inference('sup-', [status(thm)], ['47', '48'])).
% 1.05/1.25  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('51', plain,
% 1.05/1.25      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.05/1.25        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.05/1.25      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.25  thf('52', plain,
% 1.05/1.25      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.05/1.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['46', '51'])).
% 1.05/1.25  thf('53', plain,
% 1.05/1.25      (![X6 : $i, X7 : $i]:
% 1.05/1.25         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.05/1.25      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.25  thf('54', plain,
% 1.05/1.25      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.05/1.25          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.05/1.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['52', '53'])).
% 1.05/1.25  thf('55', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X0 @ X1)
% 1.05/1.25           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.05/1.25  thf('56', plain,
% 1.05/1.25      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.05/1.25          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.25             (k2_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.25      inference('sup+', [status(thm)], ['54', '55'])).
% 1.05/1.25  thf(t1_boole, axiom,
% 1.05/1.25    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.05/1.25  thf('57', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.05/1.25      inference('cnf', [status(esa)], [t1_boole])).
% 1.05/1.25  thf(t46_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.05/1.25  thf('58', plain,
% 1.05/1.25      (![X12 : $i, X13 : $i]:
% 1.05/1.25         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 1.05/1.25      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.05/1.25  thf('59', plain,
% 1.05/1.25      (![X33 : $i, X34 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.05/1.25  thf('60', plain,
% 1.05/1.25      (![X12 : $i, X13 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 1.05/1.25      inference('demod', [status(thm)], ['58', '59'])).
% 1.05/1.25  thf('61', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['57', '60'])).
% 1.05/1.25  thf(t51_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.05/1.25       ( A ) ))).
% 1.05/1.25  thf('62', plain,
% 1.05/1.25      (![X16 : $i, X17 : $i]:
% 1.05/1.25         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 1.05/1.25           = (X16))),
% 1.05/1.25      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.05/1.25  thf('63', plain,
% 1.05/1.25      (![X33 : $i, X34 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.05/1.25  thf('64', plain,
% 1.05/1.25      (![X18 : $i, X19 : $i]:
% 1.05/1.25         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 1.05/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.05/1.25  thf(l51_zfmisc_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.25  thf('65', plain,
% 1.05/1.25      (![X20 : $i, X21 : $i]:
% 1.05/1.25         ((k3_tarski @ (k2_tarski @ X20 @ X21)) = (k2_xboole_0 @ X20 @ X21))),
% 1.05/1.25      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.05/1.25  thf('66', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['64', '65'])).
% 1.05/1.25  thf('67', plain,
% 1.05/1.25      (![X20 : $i, X21 : $i]:
% 1.05/1.25         ((k3_tarski @ (k2_tarski @ X20 @ X21)) = (k2_xboole_0 @ X20 @ X21))),
% 1.05/1.25      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.05/1.25  thf('68', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['66', '67'])).
% 1.05/1.25  thf('69', plain,
% 1.05/1.25      (![X16 : $i, X17 : $i]:
% 1.05/1.25         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 1.05/1.25           = (X16))),
% 1.05/1.25      inference('demod', [status(thm)], ['62', '63', '68'])).
% 1.05/1.25  thf('70', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)) = (X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['61', '69'])).
% 1.05/1.25  thf('71', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['66', '67'])).
% 1.05/1.25  thf('72', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.05/1.25      inference('cnf', [status(esa)], [t1_boole])).
% 1.05/1.25  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['71', '72'])).
% 1.05/1.25  thf('74', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.05/1.25      inference('demod', [status(thm)], ['70', '73'])).
% 1.05/1.25  thf('75', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X0 @ X1)
% 1.05/1.25           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.05/1.25  thf('76', plain,
% 1.05/1.25      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['74', '75'])).
% 1.05/1.25  thf('77', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['57', '60'])).
% 1.05/1.25  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['76', '77'])).
% 1.05/1.25  thf('79', plain,
% 1.05/1.25      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.05/1.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['56', '78'])).
% 1.05/1.25  thf(t39_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.25  thf('80', plain,
% 1.05/1.25      (![X10 : $i, X11 : $i]:
% 1.05/1.25         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.05/1.25           = (k2_xboole_0 @ X10 @ X11))),
% 1.05/1.25      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.05/1.25  thf('81', plain,
% 1.05/1.25      (![X33 : $i, X34 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.05/1.25  thf('82', plain,
% 1.05/1.25      (![X10 : $i, X11 : $i]:
% 1.05/1.25         ((k2_xboole_0 @ X10 @ (k6_subset_1 @ X11 @ X10))
% 1.05/1.25           = (k2_xboole_0 @ X10 @ X11))),
% 1.05/1.25      inference('demod', [status(thm)], ['80', '81'])).
% 1.05/1.25  thf('83', plain,
% 1.05/1.25      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 1.05/1.25          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.25      inference('sup+', [status(thm)], ['79', '82'])).
% 1.05/1.25  thf('84', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['66', '67'])).
% 1.05/1.25  thf('85', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['71', '72'])).
% 1.05/1.25  thf('86', plain,
% 1.05/1.25      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.25      inference('demod', [status(thm)], ['83', '84', '85'])).
% 1.05/1.25  thf('87', plain,
% 1.05/1.25      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 1.05/1.25         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.25      inference('sup+', [status(thm)], ['44', '86'])).
% 1.05/1.25  thf('88', plain,
% 1.05/1.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25              (k1_tops_1 @ sk_A @ sk_B)))
% 1.05/1.25        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('89', plain,
% 1.05/1.25      (~
% 1.05/1.25       (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.05/1.25       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.25      inference('split', [status(esa)], ['88'])).
% 1.05/1.25  thf('90', plain,
% 1.05/1.25      (((k2_pre_topc @ sk_A @ sk_B)
% 1.05/1.25         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.25      inference('demod', [status(thm)], ['31', '32', '33', '42', '43'])).
% 1.05/1.25  thf('91', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(redefinition_k7_subset_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.25       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.05/1.25  thf('92', plain,
% 1.05/1.25      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.05/1.25          | ((k7_subset_1 @ X36 @ X35 @ X37) = (k4_xboole_0 @ X35 @ X37)))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.05/1.25  thf('93', plain,
% 1.05/1.25      (![X33 : $i, X34 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.05/1.25  thf('94', plain,
% 1.05/1.25      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.05/1.25         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.05/1.25          | ((k7_subset_1 @ X36 @ X35 @ X37) = (k6_subset_1 @ X35 @ X37)))),
% 1.05/1.25      inference('demod', [status(thm)], ['92', '93'])).
% 1.05/1.25  thf('95', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.05/1.25           = (k6_subset_1 @ sk_B @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['91', '94'])).
% 1.05/1.25  thf('96', plain,
% 1.05/1.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25             (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('split', [status(esa)], ['45'])).
% 1.05/1.25  thf('97', plain,
% 1.05/1.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['95', '96'])).
% 1.05/1.25  thf(t36_xboole_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.05/1.25  thf('98', plain,
% 1.05/1.25      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.05/1.25      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.05/1.25  thf('99', plain,
% 1.05/1.25      (![X33 : $i, X34 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))),
% 1.05/1.25      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.05/1.25  thf('100', plain,
% 1.05/1.25      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 1.05/1.25      inference('demod', [status(thm)], ['98', '99'])).
% 1.05/1.25  thf('101', plain,
% 1.05/1.25      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['97', '100'])).
% 1.05/1.25  thf('102', plain,
% 1.05/1.25      (![X6 : $i, X7 : $i]:
% 1.05/1.25         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.05/1.25      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.25  thf('103', plain,
% 1.05/1.25      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.05/1.25          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['101', '102'])).
% 1.05/1.25  thf('104', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k6_subset_1 @ X0 @ X1)
% 1.05/1.25           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.05/1.25      inference('demod', [status(thm)], ['15', '16'])).
% 1.05/1.25  thf('105', plain,
% 1.05/1.25      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.05/1.25          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.05/1.25             (k2_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['103', '104'])).
% 1.05/1.25  thf('106', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['76', '77'])).
% 1.05/1.25  thf('107', plain,
% 1.05/1.25      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('demod', [status(thm)], ['105', '106'])).
% 1.05/1.25  thf('108', plain,
% 1.05/1.25      (![X10 : $i, X11 : $i]:
% 1.05/1.25         ((k2_xboole_0 @ X10 @ (k6_subset_1 @ X11 @ X10))
% 1.05/1.25           = (k2_xboole_0 @ X10 @ X11))),
% 1.05/1.25      inference('demod', [status(thm)], ['80', '81'])).
% 1.05/1.25  thf('109', plain,
% 1.05/1.25      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 1.05/1.25          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['107', '108'])).
% 1.05/1.25  thf('110', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.25      inference('sup+', [status(thm)], ['66', '67'])).
% 1.05/1.25  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.25      inference('sup+', [status(thm)], ['71', '72'])).
% 1.05/1.25  thf('112', plain,
% 1.05/1.25      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.05/1.25  thf('113', plain,
% 1.05/1.25      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['90', '112'])).
% 1.05/1.25  thf('114', plain,
% 1.05/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(fc1_tops_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.05/1.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.25       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.05/1.25  thf('115', plain,
% 1.05/1.25      (![X45 : $i, X46 : $i]:
% 1.05/1.25         (~ (l1_pre_topc @ X45)
% 1.05/1.25          | ~ (v2_pre_topc @ X45)
% 1.05/1.25          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.05/1.25          | (v4_pre_topc @ (k2_pre_topc @ X45 @ X46) @ X45))),
% 1.05/1.25      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.05/1.25  thf('116', plain,
% 1.05/1.25      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.05/1.25        | ~ (v2_pre_topc @ sk_A)
% 1.05/1.25        | ~ (l1_pre_topc @ sk_A))),
% 1.05/1.25      inference('sup-', [status(thm)], ['114', '115'])).
% 1.05/1.25  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf('119', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.05/1.25      inference('demod', [status(thm)], ['116', '117', '118'])).
% 1.05/1.25  thf('120', plain,
% 1.05/1.25      (((v4_pre_topc @ sk_B @ sk_A))
% 1.05/1.25         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('sup+', [status(thm)], ['113', '119'])).
% 1.05/1.25  thf('121', plain,
% 1.05/1.25      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.05/1.25      inference('split', [status(esa)], ['88'])).
% 1.05/1.25  thf('122', plain,
% 1.05/1.25      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.05/1.25       ~
% 1.05/1.25       (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['120', '121'])).
% 1.05/1.25  thf('123', plain,
% 1.05/1.25      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.05/1.25       (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.25      inference('split', [status(esa)], ['45'])).
% 1.05/1.25  thf('124', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 1.05/1.25      inference('sat_resolution*', [status(thm)], ['89', '122', '123'])).
% 1.05/1.25  thf('125', plain, (((sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 1.05/1.25      inference('simpl_trail', [status(thm)], ['87', '124'])).
% 1.05/1.25  thf('126', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.05/1.25           = (k6_subset_1 @ sk_B @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['91', '94'])).
% 1.05/1.25  thf('127', plain,
% 1.05/1.25      (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.25      inference('demod', [status(thm)], ['4', '125', '126'])).
% 1.05/1.25  thf('128', plain,
% 1.05/1.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25              (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= (~
% 1.05/1.25             (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('split', [status(esa)], ['88'])).
% 1.05/1.25  thf('129', plain,
% 1.05/1.25      (![X0 : $i]:
% 1.05/1.25         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.05/1.25           = (k6_subset_1 @ sk_B @ X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['91', '94'])).
% 1.05/1.25  thf('130', plain,
% 1.05/1.25      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.05/1.25         <= (~
% 1.05/1.25             (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.05/1.25      inference('demod', [status(thm)], ['128', '129'])).
% 1.05/1.25  thf('131', plain,
% 1.05/1.25      (~
% 1.05/1.25       (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.05/1.25             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.05/1.25      inference('sat_resolution*', [status(thm)], ['89', '122'])).
% 1.05/1.25  thf('132', plain,
% 1.05/1.25      (((k2_tops_1 @ sk_A @ sk_B)
% 1.05/1.25         != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.05/1.25      inference('simpl_trail', [status(thm)], ['130', '131'])).
% 1.05/1.25  thf('133', plain, ($false),
% 1.05/1.25      inference('simplify_reflect-', [status(thm)], ['127', '132'])).
% 1.05/1.25  
% 1.05/1.25  % SZS output end Refutation
% 1.05/1.25  
% 1.05/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
