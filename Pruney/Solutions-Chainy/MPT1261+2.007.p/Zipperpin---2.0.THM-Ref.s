%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hFJ1JaVoiI

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:37 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 399 expanded)
%              Number of leaves         :   46 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          : 1484 (4294 expanded)
%              Number of equality atoms :  116 ( 310 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('10',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X65 @ X64 ) @ X64 )
      | ~ ( v4_pre_topc @ X64 @ X65 )
      | ~ ( l1_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X51: $i,X53: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( r1_tarski @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k6_subset_1 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X35: $i,X36: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('29',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k6_subset_1 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','27','30'])).

thf('32',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( ( k1_tops_1 @ X67 @ X66 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X67 ) @ X66 @ ( k2_tops_1 @ X67 @ X66 ) ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('39',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k6_subset_1 @ X44 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','41'])).

thf('43',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','16'])).

thf('44',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('53',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k6_subset_1 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('56',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('59',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['59','70'])).

thf('72',plain,(
    ! [X35: $i,X36: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( ( k2_pre_topc @ X63 @ X62 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X63 ) @ X62 @ ( k2_tops_1 @ X63 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k2_tops_1 @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['59','70'])).

thf('77',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['59','70'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('79',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( l1_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X56 @ X57 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('80',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('84',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76','77','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('92',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('93',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('94',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X17 @ X18 ) @ X17 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('95',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('96',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('97',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['91','98'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('100',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('101',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('102',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k6_subset_1 @ X25 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['99','102'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('104',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('105',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k6_subset_1 @ X25 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('106',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('107',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('108',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['103','110'])).

thf('112',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['88','111'])).

thf('113',plain,(
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

thf('114',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( v2_pre_topc @ X55 )
      | ( ( k2_pre_topc @ X55 @ X54 )
       != X54 )
      | ( v4_pre_topc @ X54 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','49','50','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hFJ1JaVoiI
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.13/1.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.33  % Solved by: fo/fo7.sh
% 1.13/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.33  % done 3423 iterations in 0.871s
% 1.13/1.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.33  % SZS output start Refutation
% 1.13/1.33  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.13/1.33  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.13/1.33  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.13/1.33  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.13/1.33  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.13/1.33  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.13/1.33  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.13/1.33  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.13/1.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.13/1.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.13/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.33  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.13/1.33  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.13/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.33  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.13/1.33  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.13/1.33  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.13/1.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.33  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.13/1.33  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.13/1.33  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.13/1.33  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.13/1.33  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.33  thf(t77_tops_1, conjecture,
% 1.13/1.33    (![A:$i]:
% 1.13/1.33     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.33       ( ![B:$i]:
% 1.13/1.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.33           ( ( v4_pre_topc @ B @ A ) <=>
% 1.13/1.33             ( ( k2_tops_1 @ A @ B ) =
% 1.13/1.33               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.13/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.33    (~( ![A:$i]:
% 1.13/1.33        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.13/1.33          ( ![B:$i]:
% 1.13/1.33            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.33              ( ( v4_pre_topc @ B @ A ) <=>
% 1.13/1.33                ( ( k2_tops_1 @ A @ B ) =
% 1.13/1.33                  ( k7_subset_1 @
% 1.13/1.33                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.13/1.33    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.13/1.33  thf('0', plain,
% 1.13/1.33      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33              (k1_tops_1 @ sk_A @ sk_B)))
% 1.13/1.33        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('1', plain,
% 1.13/1.33      (~
% 1.13/1.33       (((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.13/1.33       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.13/1.33      inference('split', [status(esa)], ['0'])).
% 1.13/1.33  thf(commutativity_k2_tarski, axiom,
% 1.13/1.33    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.13/1.33  thf('2', plain,
% 1.13/1.33      (![X26 : $i, X27 : $i]:
% 1.13/1.33         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 1.13/1.33      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.13/1.33  thf(t12_setfam_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.13/1.33  thf('3', plain,
% 1.13/1.33      (![X49 : $i, X50 : $i]:
% 1.13/1.33         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 1.13/1.33      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.13/1.33  thf('4', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.33      inference('sup+', [status(thm)], ['2', '3'])).
% 1.13/1.33  thf('5', plain,
% 1.13/1.33      (![X49 : $i, X50 : $i]:
% 1.13/1.33         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 1.13/1.33      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.13/1.33  thf('6', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.33      inference('sup+', [status(thm)], ['4', '5'])).
% 1.13/1.33  thf('7', plain,
% 1.13/1.33      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33             (k1_tops_1 @ sk_A @ sk_B)))
% 1.13/1.33        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('8', plain,
% 1.13/1.33      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.13/1.33      inference('split', [status(esa)], ['7'])).
% 1.13/1.33  thf('9', plain,
% 1.13/1.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf(t69_tops_1, axiom,
% 1.13/1.33    (![A:$i]:
% 1.13/1.33     ( ( l1_pre_topc @ A ) =>
% 1.13/1.33       ( ![B:$i]:
% 1.13/1.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.33           ( ( v4_pre_topc @ B @ A ) =>
% 1.13/1.33             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.13/1.33  thf('10', plain,
% 1.13/1.33      (![X64 : $i, X65 : $i]:
% 1.13/1.33         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 1.13/1.33          | (r1_tarski @ (k2_tops_1 @ X65 @ X64) @ X64)
% 1.13/1.33          | ~ (v4_pre_topc @ X64 @ X65)
% 1.13/1.33          | ~ (l1_pre_topc @ X65))),
% 1.13/1.33      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.13/1.33  thf('11', plain,
% 1.13/1.33      ((~ (l1_pre_topc @ sk_A)
% 1.13/1.33        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.13/1.33        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.13/1.33      inference('sup-', [status(thm)], ['9', '10'])).
% 1.13/1.33  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('13', plain,
% 1.13/1.33      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.13/1.33        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.13/1.33      inference('demod', [status(thm)], ['11', '12'])).
% 1.13/1.33  thf('14', plain,
% 1.13/1.33      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.13/1.33         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.13/1.33      inference('sup-', [status(thm)], ['8', '13'])).
% 1.13/1.33  thf(t28_xboole_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.13/1.33  thf('15', plain,
% 1.13/1.33      (![X14 : $i, X15 : $i]:
% 1.13/1.33         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.13/1.33      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.13/1.33  thf('16', plain,
% 1.13/1.33      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.13/1.33          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.13/1.33         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.13/1.33      inference('sup-', [status(thm)], ['14', '15'])).
% 1.13/1.33  thf('17', plain,
% 1.13/1.33      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.13/1.33          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.13/1.33         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.13/1.33      inference('sup+', [status(thm)], ['6', '16'])).
% 1.13/1.33  thf(t17_xboole_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.13/1.33  thf('18', plain,
% 1.13/1.33      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 1.13/1.33      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.13/1.33  thf(t3_subset, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.13/1.33  thf('19', plain,
% 1.13/1.33      (![X51 : $i, X53 : $i]:
% 1.13/1.33         ((m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X53)) | ~ (r1_tarski @ X51 @ X53))),
% 1.13/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.13/1.33  thf('20', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.13/1.33      inference('sup-', [status(thm)], ['18', '19'])).
% 1.13/1.33  thf(involutiveness_k3_subset_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.13/1.33       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.13/1.33  thf('21', plain,
% 1.13/1.33      (![X37 : $i, X38 : $i]:
% 1.13/1.33         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 1.13/1.33          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 1.13/1.33      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.13/1.33  thf('22', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 1.13/1.33           = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.33      inference('sup-', [status(thm)], ['20', '21'])).
% 1.13/1.33  thf('23', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.13/1.33      inference('sup-', [status(thm)], ['18', '19'])).
% 1.13/1.33  thf(d5_subset_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.13/1.33       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.13/1.33  thf('24', plain,
% 1.13/1.33      (![X31 : $i, X32 : $i]:
% 1.13/1.33         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 1.13/1.33          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 1.13/1.33      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.13/1.33  thf(redefinition_k6_subset_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.13/1.33  thf('25', plain,
% 1.13/1.33      (![X42 : $i, X43 : $i]:
% 1.13/1.33         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.13/1.33      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.33  thf('26', plain,
% 1.13/1.33      (![X31 : $i, X32 : $i]:
% 1.13/1.33         (((k3_subset_1 @ X31 @ X32) = (k6_subset_1 @ X31 @ X32))
% 1.13/1.33          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 1.13/1.33      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.33  thf('27', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.13/1.33           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.13/1.33      inference('sup-', [status(thm)], ['23', '26'])).
% 1.13/1.33  thf(dt_k6_subset_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.13/1.33  thf('28', plain,
% 1.13/1.33      (![X35 : $i, X36 : $i]:
% 1.13/1.33         (m1_subset_1 @ (k6_subset_1 @ X35 @ X36) @ (k1_zfmisc_1 @ X35))),
% 1.13/1.33      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.13/1.33  thf('29', plain,
% 1.13/1.33      (![X31 : $i, X32 : $i]:
% 1.13/1.33         (((k3_subset_1 @ X31 @ X32) = (k6_subset_1 @ X31 @ X32))
% 1.13/1.33          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 1.13/1.33      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.33  thf('30', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.13/1.33           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 1.13/1.33      inference('sup-', [status(thm)], ['28', '29'])).
% 1.13/1.33  thf('31', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 1.13/1.33           = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.33      inference('demod', [status(thm)], ['22', '27', '30'])).
% 1.13/1.33  thf('32', plain,
% 1.13/1.33      ((((k6_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.13/1.33          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.13/1.33         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.13/1.33      inference('sup+', [status(thm)], ['17', '31'])).
% 1.13/1.33  thf('33', plain,
% 1.13/1.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf(t74_tops_1, axiom,
% 1.13/1.33    (![A:$i]:
% 1.13/1.33     ( ( l1_pre_topc @ A ) =>
% 1.13/1.33       ( ![B:$i]:
% 1.13/1.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.33           ( ( k1_tops_1 @ A @ B ) =
% 1.13/1.33             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.13/1.33  thf('34', plain,
% 1.13/1.33      (![X66 : $i, X67 : $i]:
% 1.13/1.33         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 1.13/1.33          | ((k1_tops_1 @ X67 @ X66)
% 1.13/1.33              = (k7_subset_1 @ (u1_struct_0 @ X67) @ X66 @ 
% 1.13/1.33                 (k2_tops_1 @ X67 @ X66)))
% 1.13/1.33          | ~ (l1_pre_topc @ X67))),
% 1.13/1.33      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.13/1.33  thf('35', plain,
% 1.13/1.33      ((~ (l1_pre_topc @ sk_A)
% 1.13/1.33        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.13/1.33            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.13/1.33      inference('sup-', [status(thm)], ['33', '34'])).
% 1.13/1.33  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('37', plain,
% 1.13/1.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf(redefinition_k7_subset_1, axiom,
% 1.13/1.33    (![A:$i,B:$i,C:$i]:
% 1.13/1.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.13/1.33       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.13/1.33  thf('38', plain,
% 1.13/1.33      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.13/1.33         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 1.13/1.33          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 1.13/1.33      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.13/1.33  thf('39', plain,
% 1.13/1.33      (![X42 : $i, X43 : $i]:
% 1.13/1.33         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.13/1.33      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.33  thf('40', plain,
% 1.13/1.33      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.13/1.33         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 1.13/1.33          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k6_subset_1 @ X44 @ X46)))),
% 1.13/1.33      inference('demod', [status(thm)], ['38', '39'])).
% 1.13/1.33  thf('41', plain,
% 1.13/1.33      (![X0 : $i]:
% 1.13/1.33         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.13/1.33           = (k6_subset_1 @ sk_B @ X0))),
% 1.13/1.33      inference('sup-', [status(thm)], ['37', '40'])).
% 1.13/1.33  thf('42', plain,
% 1.13/1.33      (((k1_tops_1 @ sk_A @ sk_B)
% 1.13/1.33         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.13/1.33      inference('demod', [status(thm)], ['35', '36', '41'])).
% 1.13/1.33  thf('43', plain,
% 1.13/1.33      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.13/1.33          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.13/1.33         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.13/1.33      inference('sup+', [status(thm)], ['6', '16'])).
% 1.13/1.33  thf('44', plain,
% 1.13/1.33      ((((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.13/1.33          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.13/1.33         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.13/1.33      inference('demod', [status(thm)], ['32', '42', '43'])).
% 1.13/1.33  thf('45', plain,
% 1.13/1.33      (![X0 : $i]:
% 1.13/1.33         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.13/1.33           = (k6_subset_1 @ sk_B @ X0))),
% 1.13/1.33      inference('sup-', [status(thm)], ['37', '40'])).
% 1.13/1.33  thf('46', plain,
% 1.13/1.33      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33              (k1_tops_1 @ sk_A @ sk_B))))
% 1.13/1.33         <= (~
% 1.13/1.33             (((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('split', [status(esa)], ['0'])).
% 1.13/1.33  thf('47', plain,
% 1.13/1.33      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.13/1.33         <= (~
% 1.13/1.33             (((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('sup-', [status(thm)], ['45', '46'])).
% 1.13/1.33  thf('48', plain,
% 1.13/1.33      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.13/1.33         <= (~
% 1.13/1.33             (((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.13/1.33             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.13/1.33      inference('sup-', [status(thm)], ['44', '47'])).
% 1.13/1.33  thf('49', plain,
% 1.13/1.33      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.13/1.33       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.13/1.33      inference('simplify', [status(thm)], ['48'])).
% 1.13/1.33  thf('50', plain,
% 1.13/1.33      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.13/1.33       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.13/1.33      inference('split', [status(esa)], ['7'])).
% 1.13/1.33  thf('51', plain,
% 1.13/1.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('52', plain,
% 1.13/1.33      (![X37 : $i, X38 : $i]:
% 1.13/1.33         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 1.13/1.33          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 1.13/1.33      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.13/1.33  thf('53', plain,
% 1.13/1.33      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.33         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.13/1.33      inference('sup-', [status(thm)], ['51', '52'])).
% 1.13/1.33  thf('54', plain,
% 1.13/1.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('55', plain,
% 1.13/1.33      (![X31 : $i, X32 : $i]:
% 1.13/1.33         (((k3_subset_1 @ X31 @ X32) = (k6_subset_1 @ X31 @ X32))
% 1.13/1.33          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 1.13/1.33      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.33  thf('56', plain,
% 1.13/1.33      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.13/1.33         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.13/1.33      inference('sup-', [status(thm)], ['54', '55'])).
% 1.13/1.33  thf('57', plain,
% 1.13/1.33      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.33         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.13/1.33      inference('demod', [status(thm)], ['53', '56'])).
% 1.13/1.33  thf('58', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.13/1.33           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 1.13/1.33      inference('sup-', [status(thm)], ['28', '29'])).
% 1.13/1.33  thf('59', plain,
% 1.13/1.33      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.33         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.13/1.33      inference('demod', [status(thm)], ['57', '58'])).
% 1.13/1.33  thf('60', plain,
% 1.13/1.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('61', plain,
% 1.13/1.33      (![X51 : $i, X52 : $i]:
% 1.13/1.33         ((r1_tarski @ X51 @ X52) | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52)))),
% 1.13/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.13/1.33  thf('62', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.13/1.33      inference('sup-', [status(thm)], ['60', '61'])).
% 1.13/1.33  thf('63', plain,
% 1.13/1.33      (![X14 : $i, X15 : $i]:
% 1.13/1.33         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.13/1.33      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.13/1.33  thf('64', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.13/1.33      inference('sup-', [status(thm)], ['62', '63'])).
% 1.13/1.33  thf('65', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.33      inference('sup+', [status(thm)], ['4', '5'])).
% 1.13/1.33  thf(t100_xboole_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.13/1.33  thf('66', plain,
% 1.13/1.33      (![X6 : $i, X7 : $i]:
% 1.13/1.33         ((k4_xboole_0 @ X6 @ X7)
% 1.13/1.33           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.13/1.33      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.13/1.33  thf('67', plain,
% 1.13/1.33      (![X42 : $i, X43 : $i]:
% 1.13/1.33         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.13/1.33      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.33  thf('68', plain,
% 1.13/1.33      (![X6 : $i, X7 : $i]:
% 1.13/1.33         ((k6_subset_1 @ X6 @ X7)
% 1.13/1.33           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.13/1.33      inference('demod', [status(thm)], ['66', '67'])).
% 1.13/1.33  thf('69', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k6_subset_1 @ X0 @ X1)
% 1.13/1.33           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.33      inference('sup+', [status(thm)], ['65', '68'])).
% 1.13/1.33  thf('70', plain,
% 1.13/1.33      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.13/1.33         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.13/1.33      inference('sup+', [status(thm)], ['64', '69'])).
% 1.13/1.33  thf('71', plain,
% 1.13/1.33      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.33         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.13/1.33      inference('demod', [status(thm)], ['59', '70'])).
% 1.13/1.33  thf('72', plain,
% 1.13/1.33      (![X35 : $i, X36 : $i]:
% 1.13/1.33         (m1_subset_1 @ (k6_subset_1 @ X35 @ X36) @ (k1_zfmisc_1 @ X35))),
% 1.13/1.33      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.13/1.33  thf(t65_tops_1, axiom,
% 1.13/1.33    (![A:$i]:
% 1.13/1.33     ( ( l1_pre_topc @ A ) =>
% 1.13/1.33       ( ![B:$i]:
% 1.13/1.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.33           ( ( k2_pre_topc @ A @ B ) =
% 1.13/1.33             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.13/1.33  thf('73', plain,
% 1.13/1.33      (![X62 : $i, X63 : $i]:
% 1.13/1.33         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 1.13/1.33          | ((k2_pre_topc @ X63 @ X62)
% 1.13/1.33              = (k4_subset_1 @ (u1_struct_0 @ X63) @ X62 @ 
% 1.13/1.33                 (k2_tops_1 @ X63 @ X62)))
% 1.13/1.33          | ~ (l1_pre_topc @ X63))),
% 1.13/1.33      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.13/1.33  thf('74', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         (~ (l1_pre_topc @ X0)
% 1.13/1.33          | ((k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1))
% 1.13/1.33              = (k4_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.13/1.33                 (k6_subset_1 @ (u1_struct_0 @ X0) @ X1) @ 
% 1.13/1.33                 (k2_tops_1 @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1)))))),
% 1.13/1.33      inference('sup-', [status(thm)], ['72', '73'])).
% 1.13/1.33  thf('75', plain,
% 1.13/1.33      ((((k2_pre_topc @ sk_A @ 
% 1.13/1.33          (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.33           (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.13/1.33          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33             (k2_tops_1 @ sk_A @ 
% 1.13/1.33              (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.33               (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 1.13/1.33        | ~ (l1_pre_topc @ sk_A))),
% 1.13/1.33      inference('sup+', [status(thm)], ['71', '74'])).
% 1.13/1.33  thf('76', plain,
% 1.13/1.33      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.33         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.13/1.33      inference('demod', [status(thm)], ['59', '70'])).
% 1.13/1.33  thf('77', plain,
% 1.13/1.33      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.13/1.33         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.13/1.33      inference('demod', [status(thm)], ['59', '70'])).
% 1.13/1.33  thf('78', plain,
% 1.13/1.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf(dt_k2_tops_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( ( l1_pre_topc @ A ) & 
% 1.13/1.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.13/1.33       ( m1_subset_1 @
% 1.13/1.33         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.13/1.33  thf('79', plain,
% 1.13/1.33      (![X56 : $i, X57 : $i]:
% 1.13/1.33         (~ (l1_pre_topc @ X56)
% 1.13/1.33          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 1.13/1.33          | (m1_subset_1 @ (k2_tops_1 @ X56 @ X57) @ 
% 1.13/1.33             (k1_zfmisc_1 @ (u1_struct_0 @ X56))))),
% 1.13/1.33      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.13/1.33  thf('80', plain,
% 1.13/1.33      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.13/1.33         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.13/1.33        | ~ (l1_pre_topc @ sk_A))),
% 1.13/1.33      inference('sup-', [status(thm)], ['78', '79'])).
% 1.13/1.33  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('82', plain,
% 1.13/1.33      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.13/1.33        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('demod', [status(thm)], ['80', '81'])).
% 1.13/1.33  thf('83', plain,
% 1.13/1.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf(redefinition_k4_subset_1, axiom,
% 1.13/1.33    (![A:$i,B:$i,C:$i]:
% 1.13/1.33     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.13/1.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.13/1.33       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.13/1.33  thf('84', plain,
% 1.13/1.33      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.13/1.33         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 1.13/1.33          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 1.13/1.33          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 1.13/1.33      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.13/1.33  thf('85', plain,
% 1.13/1.33      (![X0 : $i]:
% 1.13/1.33         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.13/1.33            = (k2_xboole_0 @ sk_B @ X0))
% 1.13/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.13/1.33      inference('sup-', [status(thm)], ['83', '84'])).
% 1.13/1.33  thf('86', plain,
% 1.13/1.33      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.13/1.33         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.13/1.33      inference('sup-', [status(thm)], ['82', '85'])).
% 1.13/1.33  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('88', plain,
% 1.13/1.33      (((k2_pre_topc @ sk_A @ sk_B)
% 1.13/1.33         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.13/1.33      inference('demod', [status(thm)], ['75', '76', '77', '86', '87'])).
% 1.13/1.33  thf('89', plain,
% 1.13/1.33      (![X0 : $i]:
% 1.13/1.33         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.13/1.33           = (k6_subset_1 @ sk_B @ X0))),
% 1.13/1.33      inference('sup-', [status(thm)], ['37', '40'])).
% 1.13/1.33  thf('90', plain,
% 1.13/1.33      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33             (k1_tops_1 @ sk_A @ sk_B))))
% 1.13/1.33         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('split', [status(esa)], ['7'])).
% 1.13/1.33  thf('91', plain,
% 1.13/1.33      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.13/1.33         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('sup+', [status(thm)], ['89', '90'])).
% 1.13/1.33  thf(t36_xboole_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.13/1.33  thf('92', plain,
% 1.13/1.33      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 1.13/1.33      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.13/1.33  thf('93', plain,
% 1.13/1.33      (![X42 : $i, X43 : $i]:
% 1.13/1.33         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.13/1.33      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.33  thf('94', plain,
% 1.13/1.33      (![X17 : $i, X18 : $i]: (r1_tarski @ (k6_subset_1 @ X17 @ X18) @ X17)),
% 1.13/1.33      inference('demod', [status(thm)], ['92', '93'])).
% 1.13/1.33  thf(l32_xboole_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.13/1.33  thf('95', plain,
% 1.13/1.33      (![X3 : $i, X5 : $i]:
% 1.13/1.33         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.13/1.33      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.13/1.33  thf('96', plain,
% 1.13/1.33      (![X42 : $i, X43 : $i]:
% 1.13/1.33         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.13/1.33      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.33  thf('97', plain,
% 1.13/1.33      (![X3 : $i, X5 : $i]:
% 1.13/1.33         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.13/1.33      inference('demod', [status(thm)], ['95', '96'])).
% 1.13/1.33  thf('98', plain,
% 1.13/1.33      (![X0 : $i, X1 : $i]:
% 1.13/1.33         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.13/1.33      inference('sup-', [status(thm)], ['94', '97'])).
% 1.13/1.33  thf('99', plain,
% 1.13/1.33      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.13/1.33         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('sup+', [status(thm)], ['91', '98'])).
% 1.13/1.33  thf(t98_xboole_1, axiom,
% 1.13/1.33    (![A:$i,B:$i]:
% 1.13/1.33     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.13/1.33  thf('100', plain,
% 1.13/1.33      (![X24 : $i, X25 : $i]:
% 1.13/1.33         ((k2_xboole_0 @ X24 @ X25)
% 1.13/1.33           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 1.13/1.33      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.13/1.33  thf('101', plain,
% 1.13/1.33      (![X42 : $i, X43 : $i]:
% 1.13/1.33         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 1.13/1.33      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.13/1.33  thf('102', plain,
% 1.13/1.33      (![X24 : $i, X25 : $i]:
% 1.13/1.33         ((k2_xboole_0 @ X24 @ X25)
% 1.13/1.33           = (k5_xboole_0 @ X24 @ (k6_subset_1 @ X25 @ X24)))),
% 1.13/1.33      inference('demod', [status(thm)], ['100', '101'])).
% 1.13/1.33  thf('103', plain,
% 1.13/1.33      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.13/1.33          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 1.13/1.33         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('sup+', [status(thm)], ['99', '102'])).
% 1.13/1.33  thf(t1_boole, axiom,
% 1.13/1.33    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.13/1.33  thf('104', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.13/1.33      inference('cnf', [status(esa)], [t1_boole])).
% 1.13/1.33  thf('105', plain,
% 1.13/1.33      (![X24 : $i, X25 : $i]:
% 1.13/1.33         ((k2_xboole_0 @ X24 @ X25)
% 1.13/1.33           = (k5_xboole_0 @ X24 @ (k6_subset_1 @ X25 @ X24)))),
% 1.13/1.33      inference('demod', [status(thm)], ['100', '101'])).
% 1.13/1.33  thf('106', plain,
% 1.13/1.33      (![X0 : $i]:
% 1.13/1.33         ((X0) = (k5_xboole_0 @ X0 @ (k6_subset_1 @ k1_xboole_0 @ X0)))),
% 1.13/1.33      inference('sup+', [status(thm)], ['104', '105'])).
% 1.13/1.33  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.13/1.33  thf('107', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.13/1.33      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.13/1.33  thf('108', plain,
% 1.13/1.33      (![X3 : $i, X5 : $i]:
% 1.13/1.33         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.13/1.33      inference('demod', [status(thm)], ['95', '96'])).
% 1.13/1.33  thf('109', plain,
% 1.13/1.33      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.13/1.33      inference('sup-', [status(thm)], ['107', '108'])).
% 1.13/1.33  thf('110', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.13/1.33      inference('demod', [status(thm)], ['106', '109'])).
% 1.13/1.33  thf('111', plain,
% 1.13/1.33      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.13/1.33         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('demod', [status(thm)], ['103', '110'])).
% 1.13/1.33  thf('112', plain,
% 1.13/1.33      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.13/1.33         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('sup+', [status(thm)], ['88', '111'])).
% 1.13/1.33  thf('113', plain,
% 1.13/1.33      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf(t52_pre_topc, axiom,
% 1.13/1.33    (![A:$i]:
% 1.13/1.33     ( ( l1_pre_topc @ A ) =>
% 1.13/1.33       ( ![B:$i]:
% 1.13/1.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.13/1.33           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.13/1.33             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.13/1.33               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.13/1.33  thf('114', plain,
% 1.13/1.33      (![X54 : $i, X55 : $i]:
% 1.13/1.33         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 1.13/1.33          | ~ (v2_pre_topc @ X55)
% 1.13/1.33          | ((k2_pre_topc @ X55 @ X54) != (X54))
% 1.13/1.33          | (v4_pre_topc @ X54 @ X55)
% 1.13/1.33          | ~ (l1_pre_topc @ X55))),
% 1.13/1.33      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.13/1.33  thf('115', plain,
% 1.13/1.33      ((~ (l1_pre_topc @ sk_A)
% 1.13/1.33        | (v4_pre_topc @ sk_B @ sk_A)
% 1.13/1.33        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.13/1.33        | ~ (v2_pre_topc @ sk_A))),
% 1.13/1.33      inference('sup-', [status(thm)], ['113', '114'])).
% 1.13/1.33  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 1.13/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.33  thf('118', plain,
% 1.13/1.33      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.13/1.33      inference('demod', [status(thm)], ['115', '116', '117'])).
% 1.13/1.33  thf('119', plain,
% 1.13/1.33      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.13/1.33         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('sup-', [status(thm)], ['112', '118'])).
% 1.13/1.33  thf('120', plain,
% 1.13/1.33      (((v4_pre_topc @ sk_B @ sk_A))
% 1.13/1.33         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.13/1.33      inference('simplify', [status(thm)], ['119'])).
% 1.13/1.33  thf('121', plain,
% 1.13/1.33      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.13/1.33      inference('split', [status(esa)], ['0'])).
% 1.13/1.33  thf('122', plain,
% 1.13/1.33      (~
% 1.13/1.33       (((k2_tops_1 @ sk_A @ sk_B)
% 1.13/1.33          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.13/1.33             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.13/1.33       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.13/1.33      inference('sup-', [status(thm)], ['120', '121'])).
% 1.13/1.33  thf('123', plain, ($false),
% 1.13/1.33      inference('sat_resolution*', [status(thm)], ['1', '49', '50', '122'])).
% 1.13/1.33  
% 1.13/1.33  % SZS output end Refutation
% 1.13/1.33  
% 1.13/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
