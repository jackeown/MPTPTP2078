%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4EyNQucVq3

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:40 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 323 expanded)
%              Number of leaves         :   36 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          : 1124 (4000 expanded)
%              Number of equality atoms :   86 ( 258 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k2_pre_topc @ X48 @ X47 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 @ ( k2_tops_1 @ X48 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('18',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X50 @ X49 ) @ X49 )
      | ~ ( v4_pre_topc @ X49 @ X50 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','33'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('36',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['14','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k2_tops_1 @ X44 @ X43 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X44 ) @ ( k2_pre_topc @ X44 @ X43 ) @ ( k1_tops_1 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('59',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('63',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('64',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('66',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('70',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('72',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('74',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('77',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X41 @ X42 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('78',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','81'])).

thf('83',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['54'])).

thf('84',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['58','84'])).

thf('86',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['57','85'])).

thf('87',plain,
    ( $false
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['53','86'])).

thf('88',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('89',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['58','84','88'])).

thf('90',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['87','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4EyNQucVq3
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:12:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.37  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 335 iterations in 0.136s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.40/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.40/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.40/0.61  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(t77_tops_1, conjecture,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61           ( ( v4_pre_topc @ B @ A ) <=>
% 0.40/0.61             ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.61               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i]:
% 0.40/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61          ( ![B:$i]:
% 0.40/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61              ( ( v4_pre_topc @ B @ A ) <=>
% 0.40/0.61                ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.61                  ( k7_subset_1 @
% 0.40/0.61                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(dt_k2_tops_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.40/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.61       ( m1_subset_1 @
% 0.40/0.61         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (![X39 : $i, X40 : $i]:
% 0.40/0.61         (~ (l1_pre_topc @ X39)
% 0.40/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.40/0.61          | (m1_subset_1 @ (k2_tops_1 @ X39 @ X40) @ 
% 0.40/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X39))))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.61  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(redefinition_k4_subset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.40/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.61       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.40/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 0.40/0.61          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k2_xboole_0 @ X31 @ X33)))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.61            = (k2_xboole_0 @ sk_B @ X0))
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.61         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['4', '7'])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(t65_tops_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_pre_topc @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61           ( ( k2_pre_topc @ A @ B ) =
% 0.40/0.61             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X47 : $i, X48 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.40/0.61          | ((k2_pre_topc @ X48 @ X47)
% 0.40/0.61              = (k4_subset_1 @ (u1_struct_0 @ X48) @ X47 @ 
% 0.40/0.61                 (k2_tops_1 @ X48 @ X47)))
% 0.40/0.61          | ~ (l1_pre_topc @ X48))),
% 0.40/0.61      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.40/0.61            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.61  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (((k2_pre_topc @ sk_A @ sk_B)
% 0.40/0.61         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['11', '12'])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (((k2_pre_topc @ sk_A @ sk_B)
% 0.40/0.61         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['8', '13'])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61             (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.61        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('split', [status(esa)], ['15'])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(t69_tops_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_pre_topc @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61           ( ( v4_pre_topc @ B @ A ) =>
% 0.40/0.61             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X49 : $i, X50 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.40/0.61          | (r1_tarski @ (k2_tops_1 @ X50 @ X49) @ X49)
% 0.40/0.61          | ~ (v4_pre_topc @ X49 @ X50)
% 0.40/0.61          | ~ (l1_pre_topc @ X50))),
% 0.40/0.61      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.40/0.61        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.61  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.40/0.61        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.40/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['16', '21'])).
% 0.40/0.61  thf(t28_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X8 : $i, X9 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.40/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.40/0.61          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.40/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf(t100_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      (![X5 : $i, X6 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X5 @ X6)
% 0.40/0.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.40/0.61          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.61             (k2_tops_1 @ sk_A @ sk_B))))
% 0.40/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.61  thf('27', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.40/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      (![X5 : $i, X6 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X5 @ X6)
% 0.40/0.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.40/0.61  thf(t1_boole, axiom,
% 0.40/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.61  thf('30', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.40/0.61  thf(t46_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.40/0.61  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['30', '31'])).
% 0.40/0.61  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['29', '32'])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.40/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['26', '33'])).
% 0.40/0.61  thf(t98_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.40/0.61  thf('35', plain,
% 0.40/0.61      (![X16 : $i, X17 : $i]:
% 0.40/0.61         ((k2_xboole_0 @ X16 @ X17)
% 0.40/0.61           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.61          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.40/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.40/0.61  thf(t2_boole, axiom,
% 0.40/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      (![X5 : $i, X6 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X5 @ X6)
% 0.40/0.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.40/0.61  thf(t3_boole, axiom,
% 0.40/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.61  thf('40', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.61  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['39', '40'])).
% 0.40/0.61  thf('42', plain,
% 0.40/0.61      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.40/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['36', '41'])).
% 0.40/0.61  thf('43', plain,
% 0.40/0.61      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.40/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['14', '42'])).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(l78_tops_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_pre_topc @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61           ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.61             ( k7_subset_1 @
% 0.40/0.61               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.40/0.61               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      (![X43 : $i, X44 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.40/0.61          | ((k2_tops_1 @ X44 @ X43)
% 0.40/0.61              = (k7_subset_1 @ (u1_struct_0 @ X44) @ 
% 0.40/0.61                 (k2_pre_topc @ X44 @ X43) @ (k1_tops_1 @ X44 @ X43)))
% 0.40/0.61          | ~ (l1_pre_topc @ X44))),
% 0.40/0.61      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.40/0.61  thf('46', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.40/0.61            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.40/0.61  thf('49', plain,
% 0.40/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61             (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['43', '48'])).
% 0.40/0.61  thf('50', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(redefinition_k7_subset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.61       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.40/0.61  thf('51', plain,
% 0.40/0.61      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.40/0.61          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.40/0.61  thf('52', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.61  thf('53', plain,
% 0.40/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.61         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['49', '52'])).
% 0.40/0.61  thf('54', plain,
% 0.40/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61              (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('55', plain,
% 0.40/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61              (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.61         <= (~
% 0.40/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('split', [status(esa)], ['54'])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.61  thf('57', plain,
% 0.40/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.61         <= (~
% 0.40/0.61             (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('demod', [status(thm)], ['55', '56'])).
% 0.40/0.61  thf('58', plain,
% 0.40/0.61      (~
% 0.40/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.40/0.61       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.61      inference('split', [status(esa)], ['54'])).
% 0.40/0.61  thf('59', plain,
% 0.40/0.61      (((k2_pre_topc @ sk_A @ sk_B)
% 0.40/0.61         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['8', '13'])).
% 0.40/0.61  thf('60', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.61  thf('61', plain,
% 0.40/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61             (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('split', [status(esa)], ['15'])).
% 0.40/0.61  thf('62', plain,
% 0.40/0.61      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['60', '61'])).
% 0.40/0.61  thf(t36_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.61  thf('63', plain,
% 0.40/0.61      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.40/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.40/0.61  thf('64', plain,
% 0.40/0.61      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['62', '63'])).
% 0.40/0.61  thf('65', plain,
% 0.40/0.61      (![X8 : $i, X9 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.40/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.61  thf('66', plain,
% 0.40/0.61      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.40/0.61          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.61  thf('67', plain,
% 0.40/0.61      (![X5 : $i, X6 : $i]:
% 0.40/0.61         ((k4_xboole_0 @ X5 @ X6)
% 0.40/0.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.61  thf('68', plain,
% 0.40/0.61      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.40/0.61          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.61             (k2_tops_1 @ sk_A @ sk_B))))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['66', '67'])).
% 0.40/0.61  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['29', '32'])).
% 0.40/0.61  thf('70', plain,
% 0.40/0.61      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('demod', [status(thm)], ['68', '69'])).
% 0.40/0.61  thf('71', plain,
% 0.40/0.61      (![X16 : $i, X17 : $i]:
% 0.40/0.61         ((k2_xboole_0 @ X16 @ X17)
% 0.40/0.61           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.61  thf('72', plain,
% 0.40/0.61      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.61          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['70', '71'])).
% 0.40/0.61  thf('73', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['39', '40'])).
% 0.40/0.61  thf('74', plain,
% 0.40/0.61      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.40/0.61  thf('75', plain,
% 0.40/0.61      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['59', '74'])).
% 0.40/0.61  thf('76', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(fc1_tops_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.40/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.61       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.40/0.61  thf('77', plain,
% 0.40/0.61      (![X41 : $i, X42 : $i]:
% 0.40/0.61         (~ (l1_pre_topc @ X41)
% 0.40/0.61          | ~ (v2_pre_topc @ X41)
% 0.40/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.40/0.61          | (v4_pre_topc @ (k2_pre_topc @ X41 @ X42) @ X41))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.40/0.61  thf('78', plain,
% 0.40/0.61      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.40/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.40/0.61  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('81', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.40/0.61      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.40/0.61  thf('82', plain,
% 0.40/0.61      (((v4_pre_topc @ sk_B @ sk_A))
% 0.40/0.61         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['75', '81'])).
% 0.40/0.61  thf('83', plain,
% 0.40/0.61      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('split', [status(esa)], ['54'])).
% 0.40/0.61  thf('84', plain,
% 0.40/0.61      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.40/0.61       ~
% 0.40/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.40/0.61  thf('85', plain,
% 0.40/0.61      (~
% 0.40/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['58', '84'])).
% 0.40/0.61  thf('86', plain,
% 0.40/0.61      (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['57', '85'])).
% 0.40/0.61  thf('87', plain, (($false) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['53', '86'])).
% 0.40/0.61  thf('88', plain,
% 0.40/0.61      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.40/0.61       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.61          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.61             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.61      inference('split', [status(esa)], ['15'])).
% 0.40/0.61  thf('89', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['58', '84', '88'])).
% 0.40/0.61  thf('90', plain, ($false),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['87', '89'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
