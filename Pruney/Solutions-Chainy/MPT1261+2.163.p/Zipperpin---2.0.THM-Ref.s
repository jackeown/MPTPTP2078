%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2fZuEzH5y2

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 371 expanded)
%              Number of leaves         :   35 ( 119 expanded)
%              Depth                    :   16
%              Number of atoms          : 1187 (4717 expanded)
%              Number of equality atoms :   85 ( 285 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_tops_1 @ X30 @ X29 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k2_pre_topc @ X30 @ X29 ) @ ( k1_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k9_subset_1 @ X26 @ X24 @ X25 )
        = ( k3_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('31',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','31','43'])).

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
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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

thf('50',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('60',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('64',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('66',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('68',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('69',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('71',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('73',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('75',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','74'])).

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
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X27 @ X28 ) @ X27 ) ) ),
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
    inference(split,[status(esa)],['51'])).

thf('84',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('86',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['52','84','85'])).

thf('87',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['50','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('89',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','87','88'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['51'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['52','84'])).

thf('94',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2fZuEzH5y2
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 347 iterations in 0.115s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.57  thf(t77_tops_1, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.57             ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.57               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57              ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.57                ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.57                  ( k7_subset_1 @
% 0.20/0.57                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(l78_tops_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.57             ( k7_subset_1 @
% 0.20/0.57               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.57               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (![X29 : $i, X30 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.20/0.57          | ((k2_tops_1 @ X30 @ X29)
% 0.20/0.57              = (k7_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.20/0.57                 (k2_pre_topc @ X30 @ X29) @ (k1_tops_1 @ X30 @ X29)))
% 0.20/0.57          | ~ (l1_pre_topc @ X30))),
% 0.20/0.57      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.57               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.57  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.57            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57             (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.57        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['5'])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t69_tops_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57           ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.57             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X33 : $i, X34 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.20/0.57          | (r1_tarski @ (k2_tops_1 @ X34 @ X33) @ X33)
% 0.20/0.57          | ~ (v4_pre_topc @ X33 @ X34)
% 0.20/0.57          | ~ (l1_pre_topc @ X34))),
% 0.20/0.57      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.57        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.57        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.57  thf(t28_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(dt_k9_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.57         ((m1_subset_1 @ (k9_subset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X15))
% 0.20/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.20/0.57          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.57         (((k9_subset_1 @ X26 @ X24 @ X25) = (k3_xboole_0 @ X24 @ X25))
% 0.20/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.57           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.20/0.57          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['17', '20'])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['14', '21'])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.20/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 0.20/0.57          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.57            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.57          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.57  thf(l32_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.20/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf(t98_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (![X13 : $i, X14 : $i]:
% 0.20/0.57         ((k2_xboole_0 @ X13 @ X14)
% 0.20/0.57           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.57          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.20/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.57  thf(d10_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.57  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf(t36_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.20/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.57  thf('37', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      (![X13 : $i, X14 : $i]:
% 0.20/0.57         ((k2_xboole_0 @ X13 @ X14)
% 0.20/0.57           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.57  thf(t1_boole, axiom,
% 0.20/0.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.57  thf('42', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.57  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.57          = (sk_B)))
% 0.20/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['26', '31', '43'])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t65_tops_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_pre_topc @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.57           ( ( k2_pre_topc @ A @ B ) =
% 0.20/0.57             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (![X31 : $i, X32 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.20/0.57          | ((k2_pre_topc @ X32 @ X31)
% 0.20/0.57              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.20/0.57                 (k2_tops_1 @ X32 @ X31)))
% 0.20/0.57          | ~ (l1_pre_topc @ X32))),
% 0.20/0.57      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.57        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.57            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.57  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.57         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['44', '49'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57              (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (~
% 0.20/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.57       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.57      inference('split', [status(esa)], ['51'])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.57         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.20/0.57          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('split', [status(esa)], ['5'])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['56', '57'])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.20/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.20/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.57  thf('63', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.20/0.57          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['17', '20'])).
% 0.20/0.57  thf('64', plain,
% 0.20/0.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.57  thf('65', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.57            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.57          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.57  thf('67', plain,
% 0.20/0.57      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.57  thf('68', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('69', plain,
% 0.20/0.57      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.57  thf('70', plain,
% 0.20/0.57      (![X13 : $i, X14 : $i]:
% 0.20/0.57         ((k2_xboole_0 @ X13 @ X14)
% 0.20/0.57           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.57  thf('71', plain,
% 0.20/0.57      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.57          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.57  thf('72', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.57  thf('73', plain,
% 0.20/0.57      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.57  thf('74', plain,
% 0.20/0.57      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.57          = (sk_B)))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('demod', [status(thm)], ['66', '73'])).
% 0.20/0.57  thf('75', plain,
% 0.20/0.57      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['53', '74'])).
% 0.20/0.57  thf('76', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(fc1_tops_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.57       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.20/0.57  thf('77', plain,
% 0.20/0.57      (![X27 : $i, X28 : $i]:
% 0.20/0.57         (~ (l1_pre_topc @ X27)
% 0.20/0.57          | ~ (v2_pre_topc @ X27)
% 0.20/0.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.57          | (v4_pre_topc @ (k2_pre_topc @ X27 @ X28) @ X27))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.20/0.57  thf('78', plain,
% 0.20/0.57      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.57  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('81', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.57      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.20/0.57  thf('82', plain,
% 0.20/0.57      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['75', '81'])).
% 0.20/0.57  thf('83', plain,
% 0.20/0.57      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.57      inference('split', [status(esa)], ['51'])).
% 0.20/0.57  thf('84', plain,
% 0.20/0.57      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.57       ~
% 0.20/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.57  thf('85', plain,
% 0.20/0.57      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.57      inference('split', [status(esa)], ['5'])).
% 0.20/0.57  thf('86', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['52', '84', '85'])).
% 0.20/0.57  thf('87', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['50', '86'])).
% 0.20/0.57  thf('88', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.57  thf('89', plain,
% 0.20/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['4', '87', '88'])).
% 0.20/0.57  thf('90', plain,
% 0.20/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57              (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.57         <= (~
% 0.20/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('split', [status(esa)], ['51'])).
% 0.20/0.57  thf('91', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.57  thf('92', plain,
% 0.20/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.57         <= (~
% 0.20/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.57      inference('demod', [status(thm)], ['90', '91'])).
% 0.20/0.57  thf('93', plain,
% 0.20/0.57      (~
% 0.20/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.57             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['52', '84'])).
% 0.20/0.57  thf('94', plain,
% 0.20/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.57         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.20/0.57  thf('95', plain, ($false),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['89', '94'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
