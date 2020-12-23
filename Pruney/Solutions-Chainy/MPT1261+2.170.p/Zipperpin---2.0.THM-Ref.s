%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OmF5DfiRJ3

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:04 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 253 expanded)
%              Number of leaves         :   29 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  846 (3367 expanded)
%              Number of equality atoms :   57 ( 183 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_tops_1 @ X24 @ X23 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k2_pre_topc @ X24 @ X23 ) @ ( k1_tops_1 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X28 @ X27 ) @ X27 )
      | ~ ( v4_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ ( k2_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X21 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('43',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('49',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('51',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['12','49','50'])).

thf('52',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['10','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','8','52'])).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('59',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','25'])).

thf('61',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('63',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','61','62'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['12','49'])).

thf('68',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OmF5DfiRJ3
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 136 iterations in 0.062s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.51  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.19/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.51  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(t77_tops_1, conjecture,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51           ( ( v4_pre_topc @ B @ A ) <=>
% 0.19/0.51             ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.51               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]:
% 0.19/0.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51          ( ![B:$i]:
% 0.19/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51              ( ( v4_pre_topc @ B @ A ) <=>
% 0.19/0.51                ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.51                  ( k7_subset_1 @
% 0.19/0.51                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(l78_tops_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_pre_topc @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51           ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.51             ( k7_subset_1 @
% 0.19/0.51               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.19/0.51               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (![X23 : $i, X24 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.51          | ((k2_tops_1 @ X24 @ X23)
% 0.19/0.51              = (k7_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.19/0.51                 (k2_pre_topc @ X24 @ X23) @ (k1_tops_1 @ X24 @ X23)))
% 0.19/0.51          | ~ (l1_pre_topc @ X24))),
% 0.19/0.51      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.51  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.19/0.51            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t69_tops_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_pre_topc @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51           ( ( v4_pre_topc @ B @ A ) =>
% 0.19/0.51             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X27 : $i, X28 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.19/0.51          | (r1_tarski @ (k2_tops_1 @ X28 @ X27) @ X27)
% 0.19/0.51          | ~ (v4_pre_topc @ X27 @ X28)
% 0.19/0.51          | ~ (l1_pre_topc @ X28))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.19/0.51        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51             (k1_tops_1 @ sk_A @ sk_B)))
% 0.19/0.51        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.19/0.51      inference('split', [status(esa)], ['9'])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51              (k1_tops_1 @ sk_A @ sk_B)))
% 0.19/0.51        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (~
% 0.19/0.51       (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.19/0.51       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.51      inference('split', [status(esa)], ['11'])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t65_tops_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_pre_topc @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51           ( ( k2_pre_topc @ A @ B ) =
% 0.19/0.51             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (![X25 : $i, X26 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.19/0.51          | ((k2_pre_topc @ X26 @ X25)
% 0.19/0.51              = (k4_subset_1 @ (u1_struct_0 @ X26) @ X25 @ 
% 0.19/0.51                 (k2_tops_1 @ X26 @ X25)))
% 0.19/0.51          | ~ (l1_pre_topc @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.19/0.51            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(dt_k2_tops_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( l1_pre_topc @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.51       ( m1_subset_1 @
% 0.19/0.51         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X19 : $i, X20 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X19)
% 0.19/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.51          | (m1_subset_1 @ (k2_tops_1 @ X19 @ X20) @ 
% 0.19/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.19/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.19/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k4_subset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.19/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.51       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.19/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.19/0.51          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.19/0.51            = (k2_xboole_0 @ sk_B @ X0))
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.19/0.51         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['21', '24'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (((k2_pre_topc @ sk_A @ sk_B)
% 0.19/0.51         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['15', '16', '25'])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(redefinition_k7_subset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.19/0.51          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.19/0.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.19/0.51           = (k4_xboole_0 @ sk_B @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51             (k1_tops_1 @ sk_A @ sk_B))))
% 0.19/0.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.19/0.51      inference('split', [status(esa)], ['9'])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.19/0.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.19/0.51      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.51  thf(t36_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.19/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.51  thf(l32_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X0 : $i, X2 : $i]:
% 0.19/0.51         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.51  thf(t39_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (![X9 : $i, X10 : $i]:
% 0.19/0.51         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.19/0.51           = (k2_xboole_0 @ X9 @ X10))),
% 0.19/0.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.19/0.51           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.19/0.51  thf(t1_boole, axiom,
% 0.19/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.51  thf('37', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.19/0.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.19/0.51      inference('sup+', [status(thm)], ['31', '38'])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.19/0.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.19/0.51      inference('sup+', [status(thm)], ['26', '39'])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(fc1_tops_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.51       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (![X21 : $i, X22 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X21)
% 0.19/0.51          | ~ (v2_pre_topc @ X21)
% 0.19/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.51          | (v4_pre_topc @ (k2_pre_topc @ X21 @ X22) @ X21))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.51  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('46', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.19/0.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (((v4_pre_topc @ sk_B @ sk_A))
% 0.19/0.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.19/0.51      inference('sup+', [status(thm)], ['40', '46'])).
% 0.19/0.51  thf('48', plain,
% 0.19/0.51      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.19/0.51      inference('split', [status(esa)], ['11'])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.19/0.51       ~
% 0.19/0.51       (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.51  thf('50', plain,
% 0.19/0.51      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.19/0.51       (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.51      inference('split', [status(esa)], ['9'])).
% 0.19/0.51  thf('51', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['12', '49', '50'])).
% 0.19/0.51  thf('52', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['10', '51'])).
% 0.19/0.51  thf('53', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.19/0.51      inference('demod', [status(thm)], ['7', '8', '52'])).
% 0.19/0.51  thf('54', plain,
% 0.19/0.51      (![X0 : $i, X2 : $i]:
% 0.19/0.51         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.51  thf('56', plain,
% 0.19/0.51      (![X9 : $i, X10 : $i]:
% 0.19/0.51         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.19/0.51           = (k2_xboole_0 @ X9 @ X10))),
% 0.19/0.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.19/0.51         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['55', '56'])).
% 0.19/0.51  thf('58', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.51  thf('59', plain,
% 0.19/0.51      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.51  thf('60', plain,
% 0.19/0.51      (((k2_pre_topc @ sk_A @ sk_B)
% 0.19/0.51         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['15', '16', '25'])).
% 0.19/0.51  thf('61', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.51      inference('sup+', [status(thm)], ['59', '60'])).
% 0.19/0.51  thf('62', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.19/0.51           = (k4_xboole_0 @ sk_B @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.51  thf('63', plain,
% 0.19/0.51      (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['4', '61', '62'])).
% 0.19/0.51  thf('64', plain,
% 0.19/0.51      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51              (k1_tops_1 @ sk_A @ sk_B))))
% 0.19/0.51         <= (~
% 0.19/0.51             (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.19/0.51      inference('split', [status(esa)], ['11'])).
% 0.19/0.51  thf('65', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.19/0.51           = (k4_xboole_0 @ sk_B @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.51  thf('66', plain,
% 0.19/0.51      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.19/0.51         <= (~
% 0.19/0.51             (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.19/0.51      inference('demod', [status(thm)], ['64', '65'])).
% 0.19/0.51  thf('67', plain,
% 0.19/0.51      (~
% 0.19/0.51       (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.19/0.51             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['12', '49'])).
% 0.19/0.51  thf('68', plain,
% 0.19/0.51      (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.51         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 0.19/0.51  thf('69', plain, ($false),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['63', '68'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
